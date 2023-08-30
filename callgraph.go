package pointer

import (
	"go/types"

	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/ssa"
)

// CallGraph returns a call graph for the analysed program. Dynamically
// dispatched calls are resolved using the results of the pointer analysis.
func (r *Result) CallGraph() *callgraph.Graph {
	cg, ctx := r.callGraph, r.ctx

	if !r.initializedCallGraph {
		r.initializedCallGraph = true

		var prog *ssa.Program

		if len(r.Reachable) == 0 {
			goto DONE
		}

		for fun := range r.Reachable {
			prog = fun.Prog
			n := cg.CreateNode(fun)

			for _, block := range fun.Blocks {
				for _, insn := range block.Instrs {
					call, ok := insn.(ssa.CallInstruction)
					if !ok {
						continue
					}

					common := call.Common()
					v := common.Value

					var callees []*ssa.Function
					if common.IsInvoke() {
						if pt, ok := find(ctx.eval(v)).x.(tPointsTo); ok {
							find(pt.x).x.(tInterface).iterateCallees(
								prog,
								common.Method,
								func(fun *ssa.Function, _ *term) {
									callees = append(callees, fun)
								})
						}
					} else if sc := common.StaticCallee(); sc != nil {
						var funs map[*ssa.Function][]*term
						switch {
						case sc == ctx.godebug_setUpdate,
							sc == ctx.sync_runtime_registerPoolCleanup:
							funs = find(ctx.eval(common.Args[0])).x.(tClosure).funs

						case sc == ctx.time_startTimer:
							argT := sc.Signature.Params().At(0).Type().(*types.Pointer)
							runtimeTimerT := argT.Elem().Underlying().(*types.Struct)

							fI := FieldIndex(runtimeTimerT, "f")
							arg := find(ctx.eval(common.Args[0]))
							strukt := find(arg.x.(tPointsTo).x).x.(tStruct)
							closure := find(strukt.fields[fI]).x.(tClosure)
							funs = closure.funs
						}

						for fun := range funs {
							callgraph.AddEdge(cg.CreateNode(sc), nil, cg.CreateNode(fun))
						}

						callees = []*ssa.Function{sc}
					} else if _, isBuiltin := v.(*ssa.Builtin); !isBuiltin {
						closure, _ := find(ctx.eval(v)).x.(tClosure)
						for fun := range closure.funs {
							callees = append(callees, fun)
						}
					}

					for _, callee := range callees {
						callgraph.AddEdge(n, call, cg.CreateNode(callee))
					}
				}
			}
		}

		// Add call edges for runtime.SetFinalizer calls
		if runtime := prog.ImportedPackage("runtime"); runtime != nil {
			fun := runtime.Func("SetFinalizer")

			var callers []ssa.CallInstruction
			for _, ed := range cg.CreateNode(fun).In {
				callers = append(callers, ed.Site)
			}

			if len(callers) == 0 {
				goto DONE
			}

			obj := find(find(ctx.eval(fun.Params[0])).x.(tPointsTo).x).x.(tInterface)
			if obj.contents.Len() == 0 {
				goto DONE
			}

			funs := find(find(ctx.eval(fun.Params[1])).x.(tPointsTo).x).x.(tInterface)
			if funs.contents.Len() == 0 {
				goto DONE
			}

			funs.contents.Iterate(func(fType types.Type, v *term) {
				fSig, ok := fType.Underlying().(*types.Signature)
				if !ok || fSig.Recv() != nil || fSig.Params().Len() != 1 {
					return
				}

				clos, ok := find(v).x.(tClosure)
				if !ok {
					return
				}

				pType := fSig.Params().At(0).Type()
				anyWorks := false
				obj.contents.Iterate(func(oType types.Type, _ *term) {
					anyWorks = anyWorks || types.AssignableTo(oType, pType)
				})

				if anyWorks {
					for cfun := range clos.funs {
						for _, caller := range callers {
							callgraph.AddEdge(
								cg.CreateNode(caller.Parent()),
								caller,
								cg.CreateNode(cfun))

							callgraph.AddEdge(
								cg.CreateNode(fun),
								caller,
								cg.CreateNode(cfun))
						}
					}
				}
			})
		}
	DONE:
	}

	return cg
}
