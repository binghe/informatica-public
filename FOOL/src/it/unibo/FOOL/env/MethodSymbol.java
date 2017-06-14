/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.env;

import java.util.*;
import java.util.Map.*;

// CLOS-style methods
public class MethodSymbol extends ScopedSymbol {
    Map<String, Symbol> orderedArgs = new LinkedHashMap<String, Symbol>();
    List<Type> orderedArgTypes = null;
    GenericFunction gf;
    int nlocals = 0;

    public MethodSymbol(String name, Type retType, Scope parent) {
	super(name, retType, parent);
    }

    public String getName() { // canonized name with types
	Iterator<Entry<String, Symbol>> iter = orderedArgs.entrySet().iterator();
	String acc = name + "(";
	boolean first = true;
	while (iter.hasNext()) {
	    Entry<String, Symbol> entry = iter.next();
	    Symbol sym = entry.getValue();
	    Type typ = sym.getType();
	    if (!first)
		acc += ",";
	    else
		first = false;
	    acc += typ.getName();
	}
	return acc + ")";
    }

    // initialize orderedArgTypes on the first use
    public List<Type> getTypes() {
	if (orderedArgTypes == null) {
	    Iterator<Entry<String, Symbol>> iter = orderedArgs.entrySet().iterator();
	    List<Type> argTypes = new LinkedList<Type>();
	    while (iter.hasNext()) {
		Entry<String, Symbol> entry = iter.next();
		Symbol sym = entry.getValue();
		Type typ = sym.getType();
		argTypes.add(typ);
	    }
	    orderedArgTypes = argTypes;
	    return argTypes;
	} else
	    return orderedArgTypes;
    }

    // Check if the method is compatible with current generic function
    public boolean canAssignTo(Type destType) {
	if (destType instanceof GenericFunction) {
	    GenericFunction gf = (GenericFunction) destType;
	    return (this.name == gf.name && this.nargs() == gf.nargs());
	} else
	    return (this == destType);
    }

    public boolean isApplicable(List<Type> destTypes) {
	Iterator<Type> srcIter = getTypes().iterator();
	Iterator<Type> dstIter = destTypes.iterator();
	if (destTypes.size() != nargs()) return false;
	while (srcIter.hasNext()) {
	    Type srcType = srcIter.next();
	    Type dstType = dstIter.next(); // can be null here
	    if (dstType != null && !dstType.canAssignTo(srcType)) {
		return false;
	    }
	}
	return true;
    }

    // Two methods are said to agree with each other on parameter specializers
    // and qualifiers if the following conditions hold:
    // 1. Both methods have the same number of required parameters.
    // 2. For each parameter, their types are the exactly the same.
    public boolean agreeWith(MethodSymbol that) {
	if (this.nargs() != that.nargs()) return false;
	Iterator<Type> srcIter = this.getTypes().iterator();
	Iterator<Type> dstIter = that.getTypes().iterator();
	while (srcIter.hasNext()) {
	    Type thisType = srcIter.next();
	    Type thatType = dstIter.next();
	    if (thisType != thatType) return false;
	}
	return true;
    }

    // @formatter:off
    public Map<String, Symbol> getMembers() { return orderedArgs; }
    public int nargs() { return orderedArgs.size(); }
    public void setLocals(int n) { nlocals = n; }
    public int nlocals() { return nlocals; }

    public void setGenericFunction(GenericFunction gf) { this.gf = gf; }
    public GenericFunction genericFunction() { return gf; }
}
