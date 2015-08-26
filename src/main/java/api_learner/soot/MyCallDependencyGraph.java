package api_learner.soot;

/* Soot - a J*va Optimization Framework
 * Copyright (C) 2005 Antoine Mine
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

/**
 * Implementation of the paper "A Combined Pointer and Purity Analysis for
 * Java Programs" by Alexandru Salcianu and Martin Rinard, within the
 * Soot Optimization Framework.
 *
 * by Antoine Mine, 2005/01/24
 */

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import soot.SootMethod;
import soot.toolkits.graph.DirectedGraph;
import soot.util.HashMultiMap;
import soot.util.MultiMap;

/**
 * This graph captures which method in the application calls which other methods.
 * Its not a call graph. It only states if there is a call from a method A in the 
 * application to another method B in the application. 
 * We use this graph to figure out the order of inlinings we have to do when constructing the
 * actual call graph.
 */
public class MyCallDependencyGraph implements DirectedGraph<SootMethod> {

	protected Set<SootMethod> nodes;
	protected Map<SootMethod, List<SootMethod>> succ;
	protected Map<SootMethod, List<SootMethod>> pred;
	protected List<SootMethod> heads;
	protected List<SootMethod> tails;
	protected int size;

	public Set<SootMethod> getNodes() {
		return this.nodes;
	}

	public MyCallDependencyGraph(Map<SootMethod, Set<SootMethod>> callGraphMap) {
		
		this.nodes = new HashSet<SootMethod>(callGraphMap.keySet());
		MultiMap<SootMethod, SootMethod> s = new HashMultiMap<SootMethod, SootMethod>();
		MultiMap<SootMethod, SootMethod> p = new HashMultiMap<SootMethod, SootMethod>();

		for (Entry<SootMethod, Set<SootMethod>> entry : callGraphMap.entrySet()) {
			SootMethod from = entry.getKey();
			this.nodes.add(from);
			for (SootMethod to : entry.getValue()) {
				if (to.isConcrete()) {
					this.nodes.add(to);
					s.put(from, to);
					p.put(to, from);
				}
			}
		}
		// MultiMap -> Map of List
		this.succ = new HashMap<SootMethod, List<SootMethod>>();
		this.pred = new HashMap<SootMethod, List<SootMethod>>();
		this.tails = new LinkedList<SootMethod>();
		this.heads = new LinkedList<SootMethod>();
		
		for (SootMethod x : this.nodes) {
			Set<SootMethod> ss = s.get(x);
			Set<SootMethod> pp = p.get(x);
			this.succ.put(x, new LinkedList<SootMethod>(ss));
			this.pred.put(x, new LinkedList<SootMethod>(pp));
			if (ss.isEmpty())
				this.tails.add((SootMethod) x);
			if (pp.isEmpty())
				this.heads.add((SootMethod) x);
		}

		this.size = this.nodes.size();		
	}


	/** You get a List of SootMethod. */
	public List<SootMethod> getHeads() {
		return heads;
	}

	/** You get a List of SootMethod. */
	public List<SootMethod> getTails() {
		return tails;
	}

	/** You get an Iterator on SootMethod. */
	public Iterator<SootMethod> iterator() {
		return nodes.iterator();
	}

	public int size() {
		return size;
	}

	/** You get a List of SootMethod. */
	public List<SootMethod> getSuccsOf(SootMethod s) {
		return succ.get(s);
	}

	/** You get a List of SootMethod. */
	public List<SootMethod> getPredsOf(SootMethod s) {
		return pred.get(s);
	}
	
	public void toDot(String filename) {

		File fpw = new File(filename);
		try (PrintWriter pw = new PrintWriter(fpw, "utf-8");) {
			pw.println("digraph dot {");
			for (SootMethod n : this.getNodes()) {
				String shape = " shape=oval ";
				pw.println("\t\"" + n.getSignature() + "\" " + "[label=\""
						+ n.getName() + "\" " + shape + "];\n");
			}
			pw.append("\n");
			for (SootMethod from : this.getNodes()) {
				for (SootMethod to : this.getSuccsOf(from)) {
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
