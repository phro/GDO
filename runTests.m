(* ::Package:: *)

SetDirectory[NotebookDirectory[]]
Table[TestReport[i],{i,FileNames["test/*.m"]}]



