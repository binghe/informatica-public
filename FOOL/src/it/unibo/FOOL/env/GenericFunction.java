/*
 * A bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.env;

import java.util.*;
import java.util.Map.*;

// CLOS-style generic functions
public class GenericFunction extends ScopedSymbol {
    int nargs;
    Map<String, MethodSymbol> methods = new LinkedHashMap<String, MethodSymbol>();
    boolean called = false; // if it's called

    public GenericFunction(String name, Scope parent, int nargs) {
	super(name, parent);
	this.nargs = nargs;
    }

    public List<MethodSymbol> getMethods() {
	List<MethodSymbol> list = new ArrayList<MethodSymbol>(methods.values());
	return list;
    }

    public boolean addMethod(MethodSymbol method) {
	String fname = method.getName();
	if (methods.get(fname) != null) {
	    System.err.println("[addMethod] duplicated method detected: " + fname);
	    return false;
	}
	if (nargs != method.nargs()) {
	    System.err.println("[addMethod] incompatible method (nargs is different): " + fname);
	    return false;
	}
	methods.put(fname, method);
	method.setGenericFunction(this); // set back pointer
	return true;
    }

    /*
     * Given a generic function and a set of arguments, an applicable method is
     * a method for that generic function whose parameter specializers are
     * satisfied by their corresponding arguments.
     * 
     * see CLTL2 28.1.7.1. (Determining the Effective Method)
     * 
     * The effective method for a set of arguments is determined by the
     * following three-step procedure:
     * 
     * 1. Select the applicable methods.
     * 
     * 2. Sort the applicable methods by precedence order, putting the most
     * specific method first.
     * 
     * 3. Apply method combination to the sorted list of applicable methods,
     * producing the effective method. (here: the most specific method)
     */
    public List<MethodSymbol> findMethods(List<Type> argTypes) {
	Iterator<Entry<String, MethodSymbol>> iter = methods.entrySet().iterator();
	List<MethodSymbol> list = new ArrayList<MethodSymbol>();
	while (iter.hasNext()) {
	    MethodSymbol method = iter.next().getValue();
	    if (argTypes == null || method.isApplicable(argTypes)) {
		list.add(method);
	    }
	}
	Collections.sort(list, new MoreSpecificMethod());
	return list;
    }

    public MethodSymbol findMethod(List<Type> argTypes) {
	List<MethodSymbol> methods = findMethods(argTypes);
	if (methods.size() != 0)
	    return findMethods(argTypes).get(0);
	else
	    return null;
    }

    public static class MoreSpecificMethod implements Comparator<MethodSymbol> {
	public int compare(MethodSymbol o1, MethodSymbol o2) {
	    List<Type> types1 = o1.getTypes();
	    List<Type> types2 = o2.getTypes();
	    Iterator<Type> iter1 = types1.iterator();
	    Iterator<Type> iter2 = types2.iterator();
	    while (iter1.hasNext()) {
		Type type1 = iter1.next();
		Type type2 = iter2.next();
		if (type1 == type2)
		    ; // equal types, go to next loop (=)
		else if (type1.canAssignTo(type2))
		    return -1; // type1 is more specific (<)
		else
		    return 1;  // type2 is more specific (>)
	    }
	    return 0; // all equal types, which is impossible
	}
    }

    public boolean canAssignTo(Type destType) {
	if (destType instanceof MethodSymbol)
	    return (this.name == ((MethodSymbol) destType).name);
	else
	    return (this == destType);
    }

    // @formatter:off
    public Map<String, Symbol> getMembers() { return null; } // unused
    public String getName() { return name; }
    public int nargs() { return nargs; }
    public boolean called() { return called; }
    public void setCalled(boolean p) { called = p; }
}
