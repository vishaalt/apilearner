/**
 * 
 */
package api_learner.test.callgraph_test;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import api_learner.Options;
import api_learner.soot.SootToCfg;
import api_learner.test.AbstractTest;

/**
 * @author schaef
 *
 */
@RunWith(Parameterized.class)
public class CallGraphTest extends AbstractTest {

	private File sourceFile;

	@Parameterized.Parameters(name = "{index}: check ({1})")
	public static Collection<Object[]> data() {
		List<Object[]> filenames = new LinkedList<Object[]>();
		final File source_dir = new File(testRoot + "callgraph_tests/");
		File[] directoryListing = source_dir.listFiles();
		if (directoryListing != null) {
			for (File child : directoryListing) {
				if (child.isFile() && child.getName().endsWith(".java")) {
					filenames.add(new Object[] { child, child.getName() });
				} else {
					// Ignore
				}
			}
		} else {
			// Handle the case where dir is not really a directory.
			// Checking dir.isDirectory() above would not be sufficient
			// to avoid race conditions with another process that deletes
			// directories.
			throw new RuntimeException("Test data not found!");
		}
		return filenames;
	}

	public CallGraphTest(File source, String name) {
		this.sourceFile = source;
	}

	@Test
	public void test_cha() {
		testWithCallgraphAlgorithm("none");
	}	

//	@Test
//	public void test_spark() {		
//		String dotFileName = this.sourceFile.getName() + "_spark.dot";
//		Options.v().setOutFile(dotFileName);
//		testWithCallgraphAlgorithm("spark");
//	}	

	//TODO: VTA and RTA are not yet working.
//	@Test
//	public void test_vta() {		
//		testWithCallgraphAlgorithm("vta");
//	}	
	
	
	protected void testWithCallgraphAlgorithm(String algorithm) {
		soot.G.reset();
		System.out.println("Running test " + this.sourceFile.getName() + " with algorithm " + algorithm);		
		SootToCfg soot2cfg = new SootToCfg();
		Options.v().setCallGraphAlgorithm(algorithm);
		File classDir = null;
		try {
			classDir = compileJavaFile(this.sourceFile);
		} catch (IOException e) {
			e.printStackTrace();
			Assert.fail();
		}
		if (classDir==null) {
			Assert.fail();
		}
		Options.v().setNamespace("java");
		Collection<String> filenames = soot2cfg.run(classDir.getAbsolutePath());		
		
		try {
			for (String dotfileName : filenames) {
				System.err.println(dotfileName);
				String pdffileName = dotfileName.replace(".dot", ".pdf");
				Process p = Runtime.getRuntime().exec(
						"/usr/local/bin/dot -Tpdf " + dotfileName + " -o "
								+ pdffileName);
				p.waitFor();
			}
		} catch (Throwable e) {
			System.err.println(e.toString());
		}

	}
	
}
