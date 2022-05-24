SetDirectory[NotebookDirectory[]]
Echo@Directory[]
Once[Get["closed_GDO.m"]]
Once[Get["equality_test.m"]]
Once[Get["traceDegree.m"]]
reports=Table[TestReport[i],{i,FileNames["test/*.m"]}];
reports
