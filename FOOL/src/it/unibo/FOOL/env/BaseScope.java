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

public abstract class BaseScope implements Scope {
	Scope enclosingScope; // null if global (outermost) scope
	Map<String, Symbol> symbols = new LinkedHashMap<String, Symbol>();

	public BaseScope(Scope parent) { this.enclosingScope = parent; }

	int next_id = 0; // the next available ID for new variables
	public void setNextID(int n) { next_id = n; }
	public int getNextID() { return next_id; }

	public Symbol resolve(String name) {
		Symbol s = symbols.get(name);
		if (s != null)
			return s;
		// if not here, check any enclosing scope
		if (enclosingScope != null)
			return enclosingScope.resolve(name);
		return null; // not found
	}

	public void define(Symbol sym) {
		symbols.put(sym.name, sym);
		sym.scope = this;   // track the scope in each symbol
		if (sym instanceof VariableSymbol)
			sym.id = next_id++; // allocate a new ID for the var
	}

	public Scope getEnclosingScope() { return enclosingScope; }

	public String toString() {
		return symbols.keySet().toString();
	}
}
