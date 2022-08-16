SetDirectory[NotebookDirectory[]]
Get["StandardVersion.m"]
Get["closed_GDO.m"]
Get["equality_test.m"]
Get["traceDegree.m"]
Get["RVT.m"]
reports=Module[{i},Table[TestReport[i],{i,FileNames["test/*.m"]}]];
failedreports=Flatten@(Values@Values@#["TestsFailed"] & /@ reports);
failedwithmessagesreports=Flatten@(Values@#["TestsFailedWithMessages"] & /@ reports);
succeededreports=Flatten@(Values@#["TestsSucceeded"] & /@ reports);
Print["Test report summary:"]
Print[reports]
Print["Failed tests summary:"]
Print[failedreports]
