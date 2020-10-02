/*
 * Copyright (C) 2013 INRIA
 *
 * This software is governed by the CeCILL-C License under French law and
 * abiding by the rules of distribution of free software. You can use, modify
 * and/or redistribute the software under the terms of the CeCILL-C license as
 * circulated by CEA, CNRS and INRIA at http://www.cecill.info.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the CeCILL-C License for more details.
 *
 * The fact that you are presently reading this means that you have had
 * knowledge of the CeCILL-C license and that you accept its terms.
 */
package fr.inria.lille.repair.nopol;

import com.gzoltar.core.components.Statement;
import fr.inria.lille.commons.spoon.SpoonedClass;
import fr.inria.lille.commons.spoon.SpoonedProject;
import fr.inria.lille.commons.synthesis.ConstraintBasedSynthesis;
import fr.inria.lille.commons.synthesis.operator.Operator;
import fr.inria.lille.localization.CocoSpoonBasedSpectrumBasedFaultLocalizer;
import fr.inria.lille.localization.DumbFaultLocalizerImpl;
import fr.inria.lille.localization.FaultLocalizer;
import fr.inria.lille.localization.GZoltarFaultLocalizer;
import fr.inria.lille.localization.TestResult;
import fr.inria.lille.localization.metric.Ochiai;
import fr.inria.lille.repair.common.BottomTopURLClassLoader;
import fr.inria.lille.repair.common.config.NopolContext;
import fr.inria.lille.repair.common.finder.TestClassesFinder;
import fr.inria.lille.repair.common.patch.Patch;
import fr.inria.lille.repair.common.synth.RepairType;
import fr.inria.lille.repair.nopol.patch.TestPatch;
import fr.inria.lille.repair.nopol.spoon.NopolProcessor;
import fr.inria.lille.repair.nopol.spoon.NopolProcessorBuilder;
import fr.inria.lille.repair.nopol.spoon.symbolic.AssertReplacer;
import fr.inria.lille.repair.nopol.spoon.symbolic.TestExecutorProcessor;
import fr.inria.lille.repair.nopol.synth.SMTNopolSynthesizer;
import fr.inria.lille.repair.nopol.synth.Synthesizer;
import fr.inria.lille.repair.nopol.synth.SynthesizerFactory;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import org.apache.commons.io.FileUtils;
import org.json.JSONObject;
import org.junit.runner.Result;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import spoon.reflect.cu.SourcePosition;
import spoon.reflect.declaration.CtClass;
import spoon.reflect.declaration.CtType;
import utdallas.edu.profl.replicate.patchcategory.DefaultPatchCategories;
import utdallas.edu.profl.replicate.patchcategory.PatchCategory;
import utdallas.edu.profl.replicate.util.ProflResultRanking;
import xxl.java.compiler.DynamicCompilationException;
import xxl.java.junit.TestCase;
import xxl.java.junit.TestCasesListener;
import xxl.java.junit.TestSuiteExecution;

/**
 * @author Favio D. DeMarco
 */
public class NoPol {

    private FaultLocalizer localizer;

    private static int patchNum = 0;
    public static Statement currentStatement;
    private URL[] classpath;
    private final TestPatch testPatch;
    private final Logger logger = LoggerFactory.getLogger(this.getClass());
    private final SpoonedProject spooner;
    private final File[] sourceFiles;
    private String[] testClasses;
    public long startTime;
    private NopolContext nopolContext;
    private NopolResult nopolResult;
    private TestCasesListener originalTestResults;

    public NoPol(NopolContext nopolContext) {
        this.startTime = System.currentTimeMillis();
        this.nopolContext = nopolContext;
        this.classpath = nopolContext.getProjectClasspath();
        this.sourceFiles = nopolContext.getProjectSources();
        this.nopolResult = new NopolResult(nopolContext, this.startTime);

        RepairType type = nopolContext.getType();
        logger.info("Source files: " + Arrays.toString(sourceFiles));
        logger.info("Classpath: " + Arrays.toString(classpath));
        logger.info("Statement type: " + type);
        logger.info("Args: " + Arrays.toString(nopolContext.getProjectTests()));
        logger.info("Config: " + nopolContext);
        this.logSystemInformation();

        this.spooner = new SpoonedProject(this.sourceFiles, nopolContext);
        this.testClasses = nopolContext.getProjectTests();
        this.testPatch = new TestPatch(this.sourceFiles[0], this.spooner, nopolContext);

        if (this.nopolContext.isEnableProfl()) {
            this.nopolContext.getProflRank().outputSbflSus();
        }
    }

    /**
     * This getter should only be used after an error on build() method (e.g.
     * after a timeout), to get a partial result informations.
     *
     * @return
     */
    public NopolResult getNopolResult() {
        return nopolResult;
    }

    public NopolResult build() {

        System.out.println("Saving initial profl information");
        saveProflInformation();

        if (this.testClasses == null) {
            this.testClasses = new TestClassesFinder().findIn(classpath, false);
        }

        this.localizer = this.createLocalizer();

        originalTestResults = this.reRunTestCases(this.testClasses, classpath);

        System.out.println("----------------");
        logger.info(String.format("Original test suite information: totalTests=%d, failedTests=%d, passingTests=%d", originalTestResults.allTests().size(), originalTestResults.numberOfFailedTests(), originalTestResults.successfulTests().size()));
        System.out.println("----------------");

        for (TestCase tc : originalTestResults.failedTests()) {
            logger.debug(String.format("Originally failing test case %s#%s", tc.className(), tc.testName()));
        }
        System.out.println("----------------");

        for (TestCase tc : originalTestResults.successfulTests()) {
            logger.debug(String.format("Originally passing test case %s#%s", tc.className(), tc.testName()));
        }
        System.out.println("----------------");

        nopolResult.setNbTests(this.testClasses.length);
        if (nopolContext.getOracle() == NopolContext.NopolOracle.SYMBOLIC) {
            try {
                SpoonedProject jpfSpoon = new SpoonedProject(this.sourceFiles, nopolContext);
                String mainClass = "nopol.repair.NopolTestRunner";
                TestExecutorProcessor.createMainTestClass(jpfSpoon, mainClass);
                jpfSpoon.process(new AssertReplacer());

                final File outputSourceFile = new File("src-gen");
                final File outputCompiledFile = new File("target-gen");
                // generate the output file
                jpfSpoon.dumpedToClassLoader();
                jpfSpoon.generateOutputFile(outputSourceFile);
                jpfSpoon.generateOutputCompiledFile(outputCompiledFile);
            } catch (IOException e) {
                throw new RuntimeException("Unable to write transformed test", e);
            }
        }
        Map<SourceLocation, List<TestResult>> testListPerStatement = this.localizer.getTestListPerStatement();
        Map<SourceLocation, List<TestResult>> filteredTestListPerStatement = new LinkedHashMap();

        for (SourceLocation sl : testListPerStatement.keySet()) {
            for (String s : this.nopolContext.getBuggyMethods()) {
                try {
                    String methodSig = this.nopolContext.getProflRank().getMethodCoverage().getMethodFromPackageNumber(sl.getContainingClassName(), sl.getLineNumber());
                    if (s.equals(methodSig)) {
                        System.out.println("Modification point added: " + sl);
                        filteredTestListPerStatement.put(sl, testListPerStatement.get(sl));
                    }
                } catch (Exception e) {
                    System.out.println(e.getMessage());
                }
            }
        }

        if (!filteredTestListPerStatement.isEmpty()) {
            testListPerStatement = filteredTestListPerStatement;
        }

        this.nopolResult.setNbStatements(testListPerStatement.keySet().size());
        solveWithMultipleBuild(testListPerStatement);

        this.logResultInfo(this.nopolResult.getPatches());

        this.nopolResult.setDurationInMilliseconds(System.currentTimeMillis() - this.startTime);

        NopolStatus status;
        if (nopolResult.getPatches().size() > 0) {
            status = NopolStatus.PATCH;
        } else {
            if (nopolResult.getNbAngelicValues() == 0) {
                status = NopolStatus.NO_ANGELIC_VALUE;
            } else {
                status = NopolStatus.NO_SYNTHESIS;
            }
        }

        nopolResult.setNopolStatus(status);

        if (this.nopolContext.isEnableProfl()) {
            this.nopolContext.getProflRank().outputProflResults();
        }

        return this.nopolResult;
    }

    private FaultLocalizer createLocalizer() {
        switch (this.nopolContext.getLocalizer()) {
            case GZOLTAR:
                return GZoltarFaultLocalizer.createInstance(this.nopolContext);
            case DUMB:
                return new DumbFaultLocalizerImpl(this.nopolContext);
            case COCOSPOON: // default
                return new CocoSpoonBasedSpectrumBasedFaultLocalizer(this.nopolContext, new Ochiai());
            default:
                return GZoltarFaultLocalizer.createInstance(this.nopolContext);
        }
    }

    /*
	 * First algorithm of Nopol,
	 * build the initial model
	 * apply only one modification
	 * build
	 * try to find patch
     */
    private void solveWithMultipleBuild(Map<SourceLocation, List<TestResult>> testListPerStatement) {
        int n = 0;
        if (testListPerStatement.isEmpty()) {
            logger.debug("OOPS, no source /test  statements at all, no test results");
        }

        for (SourceLocation sourceLocation : testListPerStatement.keySet()) {
            n++;
            List<TestResult> tests = testListPerStatement.get(sourceLocation);

            // no failing test case executes this location
            // so there is nothing to repair here
            if (getFailingTestCasesAsList(tests).isEmpty()) {
                continue;
            }

            System.out.println("-----------------");
            logger.debug("statement/iteration #" + n);

            runOnStatement(sourceLocation, tests);

            if (!nopolContext.isEnableProfl()) {

                // patches is updated via runOnStatement
                if (nopolContext.isOnlyOneSynthesisResult() && !this.nopolResult.getPatches().isEmpty()) {
                    return;
                }
            }
        }
    }

    private void runOnStatement(SourceLocation sourceLocation, List<TestResult> tests) {

        logger.debug("Analysing {} which is executed by {} tests", sourceLocation, tests.size());
        SpoonedClass spoonCl = spooner.forked(sourceLocation.getRootClassName());
        if (spoonCl == null || spoonCl.getSimpleType() == null) {
            logger.debug("cannot spoon " + sourceLocation.toString());
            return;
        }

        NopolProcessorBuilder builder = new NopolProcessorBuilder(spoonCl.getSimpleType().getPosition().getFile(), sourceLocation.getLineNumber(), nopolContext);

        logger.debug("uniqueID=" + spoonCl.getSimpleType().hashCode());
        // here, we only collect the processors to be applied later
        // this does not change the class itself
        spoonCl.process(builder);

        final List<NopolProcessor> nopolProcessors = builder.getNopolProcessors();
        for (NopolProcessor nopolProcessor : nopolProcessors) {
            System.out.println("---");
            logger.debug("looking with " + nopolProcessor.getClass().toString());

            SourcePosition position = nopolProcessor.getTarget().getPosition();
            sourceLocation.setSourceStart(position.getSourceStart());
            sourceLocation.setSourceEnd(position.getSourceEnd());

            List<Patch> patches = executeNopolProcessor(tests, sourceLocation, spoonCl, nopolProcessor);
            this.nopolResult.addPatches(patches);

            if (!nopolContext.isEnableProfl()) {

                // patches is updated via runOnStatement
                if (nopolContext.isOnlyOneSynthesisResult() && !patches.isEmpty()) {
                    return;
                }
            }
        }
    }

    /**
     * Method used as proxy for runNopolProcessor to handle timeout
     */
    private List<Patch> executeNopolProcessor(final List<TestResult> tests, final SourceLocation sourceLocation, final SpoonedClass spoonCl, final NopolProcessor nopolProcessor) {
        final ExecutorService executor = Executors.newSingleThreadExecutor();
        final Future nopolExecution = executor.submit(
                new Callable() {
            @Override
            public Object call() throws Exception {
                return runNopolProcessor(tests, sourceLocation, spoonCl, nopolProcessor);
            }
        });
        try {
            executor.shutdown();
            return (List) nopolExecution.get(nopolContext.getMaxTimeEachTypeOfFixInMinutes(), TimeUnit.MINUTES);
        } catch (ExecutionException exception) {
            LoggerFactory.getLogger(this.getClass()).error("Error ExecutionException " + exception.toString());
            return Collections.emptyList();
        } catch (InterruptedException execption) {
            LoggerFactory.getLogger(this.getClass()).error("Repair interrupted");
            return Collections.emptyList();
        } catch (TimeoutException exception) {
            LoggerFactory.getLogger(this.getClass()).error("Timeout: execution time > " + nopolContext.getMaxTimeEachTypeOfFixInMinutes() + " " + TimeUnit.MINUTES, exception);
            return Collections.emptyList();
        }
    }

    private List<Patch> runNopolProcessor(List<TestResult> tests, SourceLocation sourceLocation, SpoonedClass spoonCl, NopolProcessor nopolProcessor) {
        String[] relevantTestCases = null;

        relevantTestCases = getFailingTestCases(tests);

        if (relevantTestCases.length == 0) {
            throw new RuntimeException("failingTestCase: nothing to repair, no failing test cases");
        }

        TestCasesListener tcl = reRunTestCases(relevantTestCases, classpath);
        Collection<TestCase> testCasesValidated = tcl.failedTests();

        if (testCasesValidated.isEmpty()) {
            throw new RuntimeException("testCasesValidated: nothing to repair, no failing test cases");
        }

        // selecting the synthesizer, typically SMT or Dynamoth
        Synthesizer synth = SynthesizerFactory.build(sourceFiles, spooner, nopolContext, sourceLocation, nopolProcessor, spoonCl);

        // Collecting the patches
        List<Patch> tmpPatches = synth.findAngelicValuesAndBuildPatch(classpath, tests, testCasesValidated, nopolContext.getMaxTimeBuildPatch(), nopolResult);

        // Final check: we recompile the patch and run all tests again
        List<Patch> finalPatches = new ArrayList<>();
        if (tmpPatches.size() > 0) {
            for (int i = 0; i < tmpPatches.size() && (true || i < nopolContext.getMaxPatches()); i++) {
                Patch patch = tmpPatches.get(i);
                TestCasesListener validationListener = isOk(patch, new LinkedList(this.originalTestResults.allTests()), synth.getProcessor());
                if (nopolContext.isEnableProfl()) {
                    Set<String> ff = new TreeSet();
                    Set<String> fp = new TreeSet();
                    Set<String> pf = new TreeSet();
                    Set<String> pp = new TreeSet();

                    for (TestCase tc : originalTestResults.failedTests()) {
                        if (validationListener.failedTests().contains(tc)) {
                            ff.add(tc.toString());
                            logger.info(String.format("[Fail->Fail] %s", tc));
                        } else {
                            fp.add(tc.toString());
                            logger.info(String.format("[Fail->Pass] %s", tc));
                        }
                    }

                    for (TestCase tc : originalTestResults.successfulTests()) {
                        if (validationListener.failedTests().contains(tc)) {
                            pf.add(tc.toString());
                            logger.info(String.format("[Pass->Fail] %s", tc));
                        } else {
                            pp.add(tc.toString());
                            // logger.info(String.format("[Pass->Pass] %s", tc));
                        }
                    }

                    logger.info(String.format("Test suite results: ff=%d, fp=%d, pf=%d, pp=%d", ff.size(), fp.size(), pf.size(), pp.size()));

                    String methodName = spoonCl.qualifiedClassName();
                    int lineNumber = patch.getLineNumber();
                    String methodSignature = this.nopolContext.getProflMethod().lookup(methodName, lineNumber);

                    if (methodSignature == null) {
                        try {
                            methodSignature = this.nopolContext.getProflMethod().getMethodFromPackageNumber(methodName, lineNumber);
                        } catch (Exception ex) {
                            logger.info(String.format("Could not find appropriate method signature for %s:%d", methodName, lineNumber));
                        }
                    }

                    logger.info("modifiedMethodSignature=" + methodSignature);
                    logger.info("lineNumber=" + lineNumber);

                    Map<String, Double> m = new TreeMap();
                    m.put(methodSignature, this.nopolContext.getProflRank().getGeneralMethodSusValues().get(methodSignature));
                    PatchCategory pc;

                    if (methodSignature != null) {
                        if (fp.size() > 0 && pf.size() == 0) {
                            if (ff.size() == 0) {
                                logger.info("Full CleanFix detected");
                                this.nopolContext.getProflRank().addCategoryEntry(DefaultPatchCategories.CLEAN_FIX_FULL, m);
                                pc = DefaultPatchCategories.CLEAN_FIX_FULL;
                            } else {
                                logger.info("Partial CleanFix detected");
                                this.nopolContext.getProflRank().addCategoryEntry(DefaultPatchCategories.CLEAN_FIX_PARTIAL, m);
                                pc = DefaultPatchCategories.CLEAN_FIX_PARTIAL;
                            }
                        } else if (fp.size() > 0 && pf.size() > 0) {
                            if (ff.size() == 0) {
                                logger.info("Full NoisyFix detected");
                                this.nopolContext.getProflRank().addCategoryEntry(DefaultPatchCategories.NOISY_FIX_FULL, m);
                                pc = DefaultPatchCategories.NOISY_FIX_FULL;
                            } else {
                                logger.info("Partial NoisyFix detected");
                                this.nopolContext.getProflRank().addCategoryEntry(DefaultPatchCategories.NOISY_FIX_PARTIAL, m);
                                pc = DefaultPatchCategories.NOISY_FIX_PARTIAL;
                            }
                        } else if (fp.size() == 0 && pf.size() == 0) {
                            logger.info("NoneFix detected");
                            this.nopolContext.getProflRank().addCategoryEntry(DefaultPatchCategories.NONE_FIX, m);
                            pc = DefaultPatchCategories.NONE_FIX;
                        } else {
                            logger.info("NegFix detected");
                            this.nopolContext.getProflRank().addCategoryEntry(DefaultPatchCategories.NEG_FIX, m);
                            pc = DefaultPatchCategories.NEG_FIX;
                        }

                        saveProflInformation();
                        savePatchInformation(methodSignature, patch, ++patchNum);
                        saveTestInformation(ff, fp, pf, pp, pc, methodSignature, lineNumber);
                    } else {
                        System.out.println(String.format("Could not find information for %s %d", methodName, lineNumber));
                    }

                }

                if (nopolContext.isSkipRegressionStep() || validationListener.failedTests().isEmpty()) {
                    finalPatches.add(patch);
                } else {
                    logger.debug("Could not find a valid patch in {}", sourceLocation);
                }
            }

            logger.debug("Skipped {} patches for sake of performance", Math.max(0, tmpPatches.size() - nopolContext.getMaxPatches()));
        }

        return finalPatches;
    }

    private TestCasesListener isOk(Patch newRepair, List<TestCase> testClasses, NopolProcessor processor) {
        logger.trace("Suggested patch: {}", newRepair);
        try {
            return testPatch.passesAllTests(newRepair, testClasses, processor);
        } catch (DynamicCompilationException e) {
            logger.error("Patch malformed " + newRepair.asString(), e);
            throw new RuntimeException("invalid patch");
        }
    }

    private List<TestCase> getFailingTestCasesAsList(List<TestResult> tests) {
        List<TestCase> failingClassTest = new ArrayList<>();
        for (int i = 0; i < tests.size(); i++) {
            TestResult testResult = tests.get(i);
            if (!testResult.isSuccessful()) {

                failingClassTest.add(testResult.getTestCase());
            }
        }
        return failingClassTest;
    }

    private String[] getFailingTestCases(List<TestResult> tests) {
        List<TestCase> failingTests = getFailingTestCasesAsList(tests);
        String[] array = new String[failingTests.size()];
        for (int i = 0; i < failingTests.size(); i++) {
            array[i] = failingTests.get(i).className();
        }
        return array;
    }

    private String[] convertTestCasesToArray(List<TestResult> tests) {
        String[] array = new String[tests.size()];
        for (int i = 0; i < tests.size(); i++) {
            array[i] = tests.get(i).getTestCase().className();
        }
        return array;
    }

    private TestCasesListener reRunTestCases(String[] testClasses, URL[] deps) {
        TestCasesListener listener = new TestCasesListener();
        Result r = TestSuiteExecution.runCasesIn(testClasses, new BottomTopURLClassLoader(deps, Thread.currentThread().getContextClassLoader()), listener, this.nopolContext);
        return listener;
    }

    public SpoonedProject getSpooner() {
        return spooner;
    }

    public FaultLocalizer getLocalizer() {
        return localizer;
    }

    private void logSystemInformation() {
        this.logger.info("Available processors (cores): " + Runtime.getRuntime().availableProcessors());

        /* Total amount of free memory available to the JVM */
        this.logger.info("Free memory: " + FileUtils.byteCountToDisplaySize(Runtime.getRuntime().freeMemory()));

        /* This will return Long.MAX_VALUE if there is no preset limit */
        long maxMemory = Runtime.getRuntime().maxMemory();
        /* Maximum amount of memory the JVM will attempt to use */
        this.logger.info("Maximum memory: "
                + (maxMemory == Long.MAX_VALUE ? "no limit" : FileUtils.byteCountToDisplaySize(maxMemory)));

        /* Total memory currently available to the JVM */
        this.logger.info("Total memory available to JVM: "
                + FileUtils.byteCountToDisplaySize(Runtime.getRuntime().totalMemory()));

        this.logger.info("Java version: " + Runtime.class.getPackage().getImplementationVersion());
        this.logger.info("JAVA_HOME: " + System.getenv("JAVA_HOME"));
        this.logger.info("PATH: " + System.getenv("PATH"));
    }

    private void logResultInfo(List<Patch> patches) {
        long durationTime = System.currentTimeMillis() - this.startTime;
        this.logger.info("----INFORMATION----");
        List<CtType<?>> allClasses = this.getSpooner().spoonFactory().Class().getAll();
        int nbMethod = 0;
        for (int i = 0; i < allClasses.size(); i++) {
            CtType<?> ctSimpleType = allClasses.get(i);
            if (ctSimpleType instanceof CtClass) {
                Set methods = ((CtClass) ctSimpleType).getMethods();
                nbMethod += methods.size();
            }
        }

        this.logger.info("Nb classes : " + allClasses.size());
        this.logger.info("Nb methods : " + nbMethod);
        if (NoPol.currentStatement != null) {
            BitSet coverage = NoPol.currentStatement.getCoverage();
            int countStatementSuccess = 0;
            int countStatementFailed = 0;
            int nextTest = coverage.nextSetBit(0);
            /*while (nextTest != -1) {
				TestResultImpl testResult = nopol.getgZoltar().getGzoltar().getTestResults().get(nextTest);
				if (testResult.wasSuccessful()) {
					countStatementSuccess += testResult.getCoveredComponents().size();
				} else {
					countStatementFailed += testResult.getCoveredComponents().size();
				}
				nextTest = coverage.nextSetBit(nextTest + 1);
			}*/

            this.logger.info("Nb statement executed by the passing tests of the patched line: " + countStatementSuccess);
            this.logger.info("Nb statement executed by the failing tests of the patched line: " + countStatementFailed);
        }

        this.logger.info("Nb Statements Analyzed : " + SynthesizerFactory.getNbStatementsAnalysed());
        this.logger.info("Nb Statements with Angelic Value Found : " + SMTNopolSynthesizer.getNbStatementsWithAngelicValue());
        if (nopolContext.getSynthesis() == NopolContext.NopolSynthesis.SMT) {
            this.logger.info("Nb inputs in SMT : " + SMTNopolSynthesizer.getDataSize());
            this.logger.info("Nb SMT level: " + ConstraintBasedSynthesis.level);
            if (ConstraintBasedSynthesis.operators != null) {
                this.logger.info("Nb SMT components: [" + ConstraintBasedSynthesis.operators.size() + "] " + ConstraintBasedSynthesis.operators);
                Iterator<Operator<?>> iterator = ConstraintBasedSynthesis.operators.iterator();
                Map<Class, Integer> mapType = new HashMap<>();
                while (iterator.hasNext()) {
                    Operator<?> next = iterator.next();
                    if (!mapType.containsKey(next.type())) {
                        mapType.put(next.type(), 1);
                    } else {
                        mapType.put(next.type(), mapType.get(next.type()) + 1);
                    }
                }
                for (Iterator<Class> patchIterator = mapType.keySet().iterator(); patchIterator.hasNext();) {
                    Class next = patchIterator.next();
                    this.logger.info("                  " + next + ": " + mapType.get(next));
                }
            }

            this.logger.info("Nb variables in SMT : " + SMTNopolSynthesizer.getNbVariables());
        }
        //this.logger.info("Nb run failing test  : " + nbFailingTestExecution);
        //this.logger.info("Nb run passing test : " + nbPassedTestExecution);

        this.logger.info("NoPol Execution time : " + durationTime + "ms");
        this.logger.info("".equals(nopolContext.getIdentifier()) ? "" : "  for " + nopolContext.getIdentifier());

        if (patches != null && !patches.isEmpty()) {
            this.logger.info("----PATCH FOUND----");
            for (int i = 0; i < patches.size(); i++) {
                Patch patch = patches.get(i);
                this.logger.info(patch.asString());
                this.logger.info("Nb test that executes the patch: " + this.getLocalizer().getTestListPerStatement().get(patch.getSourceLocation()).size());
                this.logger.info(String.format("%s:%d: %s", patch.getSourceLocation().getContainingClassName(), patch.getLineNumber(), patch.getType()));
                String diffPatch = patch.toDiff(this.getSpooner().spoonFactory(), nopolContext);
                this.logger.info(diffPatch);

                if (nopolContext.getOutputFolder() != null) {
                    File patchLocation = new File(nopolContext.getOutputFolder() + "/patch_" + (i + 1) + ".diff");
                    try {
                        PrintWriter writer = new PrintWriter(patchLocation, "UTF-8");
                        writer.print(diffPatch);
                        writer.close();
                    } catch (IOException e) {
                        System.err.println("Unable to write the patch: " + e.getMessage());
                    }
                }
            }
        }
        if (nopolContext.isJson()) {
            JSONObject output = new JSONObject();

            output.put("nb_classes", allClasses.size());
            output.put("nb_methods", nbMethod);
            output.put("nbStatement", SynthesizerFactory.getNbStatementsAnalysed());
            output.put("nbAngelicValue", SMTNopolSynthesizer.getNbStatementsWithAngelicValue());
            //output.put("nb_failing_test", nbFailingTestExecution);
            //output.put("nb_passing_test", nbPassedTestExecution);
            output.put("executionTime", durationTime);
            output.put("date", new Date());
            if (patches != null) {
                for (int i = 0; i < patches.size(); i++) {
                    Patch patch = patches.get(i);

                    JSONObject patchOutput = new JSONObject();

                    JSONObject locationOutput = new JSONObject();
                    locationOutput.put("class", patch.getSourceLocation().getContainingClassName());
                    locationOutput.put("line", patch.getLineNumber());
                    patchOutput.put("patchLocation", locationOutput);
                    patchOutput.put("patchType", patch.getType());
                    patchOutput.put("nb_test_that_execute_statement", this.getLocalizer().getTestListPerStatement().get(patch.getSourceLocation()).size());
                    patchOutput.put("patch", patch.toDiff(this.getSpooner().spoonFactory(), nopolContext));

                    output.append("patch", patchOutput);
                }
            }

            try (FileWriter writer = new FileWriter(nopolContext.getOutputFolder() + "/output.json")) {
                output.write(writer);
                writer.close();
            } catch (IOException ignore) {
            }
        }
    }

    private void saveProflInformation() {
        ProflResultRanking profl = this.nopolContext.getProflRank();

        File genOutputFile = new File(String.format("%s/generalSusInfo.profl", this.nopolContext.getOutputFolder()));
        writeToFile(profl.outputSbflSus(), genOutputFile);

        File proflOutputFile = new File(String.format("%s/aggregatedSusInfo.profl", this.nopolContext.getOutputFolder()));
        writeToFile(profl.outputProflResults(), proflOutputFile);

        File catOutputFile = new File(String.format("%s/category_information.profl", this.nopolContext.getOutputFolder()));
        writeToFile(profl.outputProflCatInfo(), catOutputFile);
    }

    private void savePatchInformation(String methodSig, Patch patch, int patchNum) {
        File patchOutputFile = new File(String.format("%s/patches/%d.patch", this.nopolContext.getOutputFolder(), patchNum));
        LinkedList<String> messages = new LinkedList();
        messages.add(String.format("Parent class: %s", patch.getRootClassName()));
        messages.add(String.format("Method signature: %s", methodSig));
        messages.add(String.format("Patched lines %d", patch.getLineNumber()));
        messages.add(String.format("Patch type: %s", patch.getType().name()));
        messages.add(String.format("Current time: %d", System.currentTimeMillis()));
        messages.add("-------------");
        messages.add(patch.asString());
        writeToFile(messages, patchOutputFile);
    }

    private void writeToFile(Collection<String> message, File output) {
        System.out.println(String.format("Saving to %s", output.getAbsolutePath()));
        output.getParentFile().mkdirs();
        try (BufferedWriter bw = new BufferedWriter(new FileWriter(output))) {
            for (String s : message) {
                bw.write(s);
                bw.newLine();
            }
        } catch (IOException ex) {
            System.out.println("Could not write to file: " + output);
            System.out.println(ex.getMessage());
        }

    }

    private void saveTestInformation(Set<String> ff, Set<String> fp, Set<String> pf, Set<String> pp, PatchCategory pc, String methodName, int lineNumber) {
        File patchOutputFile = new File(String.format("%s/tests/%d.tests", this.nopolContext.getOutputFolder(), patchNum));
        LinkedList<String> messages = new LinkedList();
        messages.add(String.format("Test suite results: ff=%d, fp=%d, pf=%d, pp=%d", ff.size(), fp.size(), pf.size(), pp.size()));
        messages.add(String.format("Modified method: %s", methodName));
        messages.add(String.format("Modified line: %d", lineNumber));
        messages.add(String.format("PatchCategory: %s", pc.getCategoryName()));
        messages.add("-------------");

        for (String s : ff) {
            messages.add(String.format("[Fail->Fail] %s", s));
        }

        for (String s : fp) {
            messages.add(String.format("[Fail->Pass] %s", s));
        }

        for (String s : pf) {
            messages.add(String.format("[Pass->Fail] %s", s));
        }

        writeToFile(messages, patchOutputFile);
    }
}
