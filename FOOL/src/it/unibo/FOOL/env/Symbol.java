/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.env;

/***
 * Excerpted from "Language Implementation Patterns", published by The Pragmatic
 * Bookshelf. Copyrights apply to this code. It may not be used to create
 * training material, courses, books, articles, and the like. Contact us if you
 * are in doubt. We make no guarantees that this code is fit for any purpose.
 * Visit http://www.pragmaticprogrammer.com/titles/tpdsl for more book
 * information.
 ***/

/*
 * Modified by Chun Tian, while it's still language independent.
 */

public class Symbol {
    String name;  // All symbols at least have a name
    String cname; // A "code name" for code generation
    Scope scope;  // All symbols know what scope contains them.
    Type type;

    public Symbol(String name, Type type) {
	this(name);
	this.type = type;
    }

    // @formatter:off
    public Symbol(String name) { this.name = name; }
    public String getName() { return name; }
    public Scope getScope() { return scope; }
    public Type getType() { return type; }
    public String cname() { return cname; }
    public void set_cname(String name) { cname = name; }
    // @formatter:on

    public String toString() {
	String s = "";
	if (scope != null) {
	    s = scope.getScopeName() + ".";
	}
	if (type != null) {
	    return '<' + s + getName() + ":" + type + '>';
	}
	return s + getName();
    }

    public static String stripBrackets(String s) {
	return s.substring(1, s.length() - 1);
    }
}
