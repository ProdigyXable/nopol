package xxl.java.junit;

import com.gzoltar.core.instr.testing.TestResult;
import org.junit.runner.JUnitCore;
import org.junit.runner.Request;
import org.junit.runner.Result;
import org.junit.runner.notification.RunListener;

import java.util.concurrent.Callable;

public class JUnitSingleTestResultRunner implements Callable<Result> {

	private final String testName;
	private final String className;

	public JUnitSingleTestResultRunner(TestResult testCase, RunListener listener) {
		this.testCase = testCase;
		this.listener = listener;
		String[] split = testCase.getName().split("#");
		this.testName = split[1];
		this.className = split[0];
	}

	@Override
	public Result call() throws Exception {
		JUnitCore runner = new JUnitCore();
		runner.addListener(listener);
		Request request = Request.method(testClassFromCustomClassLoader(), testCaseName());
		return runner.run(request);
	}
	
	private Class<?> testClassFromCustomClassLoader() {
		Class<?> compiledClass; 
		try {
			compiledClass = Thread.currentThread().getContextClassLoader().loadClass(testClassName());
		} catch (ClassNotFoundException cnfe) {
			throw new RuntimeException(cnfe);
		}
		return compiledClass;
	}
	
	public String testCaseName() {
		return testName;
	}
	
	public String testClassName() {
		return className;
	}

	private TestResult testCase;
	private RunListener listener;
}
