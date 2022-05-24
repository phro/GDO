SetDirectory[NotebookDirectory[]]
Echo@Directory[]
Get["StandardVersion.m"]
Get["closed_GDO.m"]
Get["equality_test.m"]
Get["traceDegree.m"]
reports=Module[{i},Table[TestReport[i],{i,FileNames["test/*.m"]}]];
reports
