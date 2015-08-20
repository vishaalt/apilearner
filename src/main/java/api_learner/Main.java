/**
 * 
 */
package api_learner;

import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;

import api_learner.soot.SootToCfg;
import api_learner.util.Log;


public class Main {

	public static void main(String[] args) {
		Options options = Options.v();
		CmdLineParser parser = new CmdLineParser(options);
		try {
			// parse command-line arguments
			parser.parseArgument(args);
			SootToCfg soot2cfg = new SootToCfg();
			soot2cfg.run(Options.v().getJavaInput());
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