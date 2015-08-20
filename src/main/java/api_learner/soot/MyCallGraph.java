/**
 * 
 */
package api_learner.soot;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import soot.SootMethod;

/**
 * @author schaef
 *
 */
public enum MyCallGraph {
	INSTANCE;
	public static MyCallGraph v() {
		return INSTANCE;
	}

	private Set<SootMethod> nodes = new HashSet<SootMethod>();
	private Map<SootMethod, Set<SootMethod>> edges = new HashMap<SootMethod, Set<SootMethod>>();

	public void addEdge(SootMethod from, SootMethod to) {
		this.nodes.add(from);
		this.nodes.add(to);

		if (!this.edges.containsKey(from)) {
			this.edges.put(from, new HashSet<SootMethod>());
		}
		this.edges.get(from).add(to);
	}

	public void toDot(String filename) {
		File fpw = new File(filename);
		try (PrintWriter pw = new PrintWriter(fpw, "utf-8");) {
			pw.println("digraph dot {");
			for (SootMethod m : this.nodes) {
				String shape = " shape=oval ";
				pw.println("\t\"" + m.getSignature() + "\" " + "[label=\""
						+ m.getSignature() + "\" " + shape + "];\n");
			}
			pw.append("\n");
			for (Entry<SootMethod, Set<SootMethod>> e : this.edges.entrySet()) {
				SootMethod from = e.getKey();
				for (SootMethod to : e.getValue()) {
					pw.append("\t\"" + from.getSignature() + "\" -> \""
							+ to.getSignature() + "\";\n");
				}
			}

			pw.println("}");
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
