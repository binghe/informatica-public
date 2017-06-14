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
 * Modified by Chun Tian with the following changes:
 * - Added slot "initFunction" and get/set methods;
 * - Re-designed canAssignTo();
 */

import java.util.*;

public class ClassSymbol extends ScopedSymbol implements Type {
    static public final String top = "standard_object";
    private int typeIndex;
    static int nextTypeIndex = 100;
    MethodSymbol initFunction, newFunction;
    List<ClassSymbol> local_precedence_list;

    /**
     * This is the superclass not enclosingScope field. We still record the
     * enclosing scope so we can push in and pop out of class defs.
     */
    ClassSymbol superClass;

    /** List of all fields and methods */
    public Map<String, Symbol> members = new LinkedHashMap<String, Symbol>();

    public ClassSymbol(String name, Scope enclosingScope, ClassSymbol superClass) {
	super(name, enclosingScope);
	this.superClass = superClass;
	this.typeIndex = nextTypeIndex++;
	// compute local precedence list
	List<ClassSymbol> list = new LinkedList<ClassSymbol>();
	ClassSymbol t = this;
	while (t != null) {
	    list.add(t);
	    t = t.superClass;
	}
	local_precedence_list = list;
    }

    public Scope getParentScope() {
	if (superClass == null) return enclosingScope; // globals
	return superClass; // if not Object, return super
    }

    /** For a.b, only look in a's class hierarchy to resolve b, not globals */
    public Symbol resolveMember(String name) {
	Symbol s = members.get(name);
	if (s != null) return s;
	// if not here, check any enclosing scope
	if (superClass != null) {
	    return superClass.resolveMember(name);
	}
	return null; // not found
    }

    // get an ordered list of class and its direct superclasses.
    public List<ClassSymbol> getLocalPrecedenceList() {
	return local_precedence_list;
    }

    /** Return true if 'ancestor' is this class or above in hierarchy */
    public boolean isInstanceof(ClassSymbol ancestor) {
	ClassSymbol t = this;
	while (t != null) {
	    if (t == ancestor) return true;
	    t = t.superClass;
	}
	return false;
    }

    public String toString() {
	return "class " + name + "(" + superClass.name + "):{" + stripBrackets(members.keySet().toString()) + "}";
    }

    public boolean canAssignTo(Type destType) {
	if (destType == null)
	    return true;
	else if (destType instanceof ClassSymbol)
	    return isInstanceof((ClassSymbol) destType);
	else
	    return (this == destType);
    }

    // @formatter:off
    public int getTypeIndex() { return typeIndex; }
    public Map<String, Symbol> getMembers() { return members; }
    public void setInitFunction(MethodSymbol fun) { initFunction = fun; }
    public MethodSymbol initFunction() { return initFunction; }
    public void setNewFunction(MethodSymbol fun) { newFunction = fun; }
    public MethodSymbol newFunction() { return newFunction; }
}
