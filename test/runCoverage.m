Needs["Instrumentation`"]
Needs["CodeParser`"]
baseline = CoverageInstrument["../src/","coverage/"]
{res, runData} = 
        CoverageEvaluate[
                Get["coverage/newVersion.m"]
                Get["coverage/RVT.m"]
                Get["runTests.m"]
]
CoverageProcess[baseline, "coverage", "coverage-baseline.lcov"]
CoverageProcess[runData , "coverage", "coverage-runData.lcov" ]
