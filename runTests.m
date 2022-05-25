SetDirectory[NotebookDirectory[]]
Get["StandardVersion.m"]
Get["closed_GDO.m"]
Get["equality_test.m"]
Get["traceDegree.m"]
reports=Module[{i},Table[TestReport[i],{i,FileNames["test/*.m"]}]];
failedreports=Flatten@(Values@Values@#["TestsFailed"] & /@ reports);
Print["Test report summary:"]
Print[reports]
Print["Failed tests summary:"]
Print[failedreports]
