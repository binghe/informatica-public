/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.env;

/***
 * Excerpted from "Language Implementation Patterns",
 * published by The Pragmatic Bookshelf.
 * Copyrights apply to this code. It may not be used to create training material, 
 * courses, books, articles, and the like. Contact us if you are in doubt.
 * We make no guarantees that this code is fit for any purpose. 
 * Visit http://www.pragmaticprogrammer.com/titles/tpdsl for more book information.
***/

/*
 * Modified by Chun Tian, while it's still language independent.
 */

import java.util.*;

public class MethodSymbol extends ScopedSymbol {
	Map<String, Symbol> orderedArgs = new LinkedHashMap<String, Symbol>();

	public MethodSymbol(String name, Type retType, Scope parent) {
		super(name, retType, parent);
	}

	public Map<String, Symbol> getMembers() { return orderedArgs; }

	public String getName() {
		return name + "(" + stripBrackets(orderedArgs.keySet().toString()) + ")";
	}

	public int nargs() { return orderedArgs.size(); } // unused
	
	int nlocals = 0;
	public void setLocals(int n) { nlocals = n; }
	public int nlocals() { return nlocals; }
}
