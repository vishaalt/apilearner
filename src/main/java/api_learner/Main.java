/**
 * 
 */
package api_learner;

import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;

import api_learner.soot.SootToCfg;
import api_learner.util.Log;

import javax.crypto.Cipher;

public class Main {

	public static void main(String[] args) throws Exception {
		Options options = Options.v();
		CmdLineParser parser = new CmdLineParser(options);
		try {
			// something for guru
			Cipher c = Cipher.getInstance("DES");
			System.err.println(c);
	
			// parse command-line arguments
			parser.parseArgument(args);
			SootToCfg soot2cfg = new SootToCfg();
			soot2cfg.run(Options.v().getJavaInput());
			System.err.println("Written output to "+ Options.v().getOutFileDirName());
		} catch (CmdLineException e) {
			Log.error(e.toString());
			Log.error("java -jar apilearner.jar [options...] arguments...");
			parser.printUsage(System.out);
		} catch (Throwable t) {
			Log.error(t.toString());
			throw t;
		} finally {
			Options.resetInstance();
			soot.G.reset();
		}
	}

}