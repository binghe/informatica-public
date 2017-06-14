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

import java.util.Map;

public abstract class ScopedSymbol extends Symbol implements Scope {
    Scope enclosingScope;
    int next_id = 0; // the next available ID for new symbols

    public ScopedSymbol(String name, Type type, Scope enclosingScope) {
	super(name, type);
	this.enclosingScope = enclosingScope;
    }

    public ScopedSymbol(String name, Scope enclosingScope) {
	super(name);
	this.enclosingScope = enclosingScope;
    }

    public Symbol resolve(String name) {
	Symbol s = getMembers().get(name);
	if (s != null) return s;
	// if not here, check any enclosing scope
	if (getEnclosingScope() != null) {
	    return getEnclosingScope().resolve(name);
	}
	return null; // not found
    }

    public void define(Symbol sym) {
	getMembers().put(sym.name, sym);
	sym.scope = this; // track the scope in each symbol
	if (sym instanceof VariableSymbol) {
	    VariableSymbol var = (VariableSymbol) sym;
	    var.id = next_id++; // allocate a new ID for the var
	}
    }

    /*
     * Indicate how subclasses store scope members. Allows us to factor out
     * common code in this class.
     */
    public abstract Map<String, Symbol> getMembers();

    // @formatter:off
    public Symbol resolveType(String name) { return resolve(name); }
    public Scope getEnclosingScope() { return enclosingScope; }
    public String getScopeName() { return name; }
    public int getNextID() { return next_id; }
    public void setNextID(int n) { next_id = n; }
}
