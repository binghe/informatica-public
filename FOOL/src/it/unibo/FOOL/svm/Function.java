/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.svm;

import java.io.*;

/***
 * Excerpted from "Language Implementation Patterns", published by The Pragmatic
 * Bookshelf. Copyrights apply to this code. It may not be used to create
 * training material, courses, books, articles, and the like. Contact us if you
 * are in doubt. We make no guarantees that this code is fit for any purpose.
 * Visit http://www.pragmaticprogrammer.com/titles/tpdsl for more book
 * information.
 ***/

public class Function implements Serializable {
    private static final long serialVersionUID = -8903239810580923122L;
    String name;
    int nargs;
    int nlocals;
    int address;

    public Function(String name, int nargs, int nlocals, int address) {
	this.name = name;
	this.nargs = nargs;
	this.nlocals = nlocals;
	this.address = address;
    }

    // @formatter:off
    public Function(String name) { this.name = name; }
    public int hashCode() { return name.hashCode(); }

    // @formatter:on
    public boolean equals(Object o) {
	return (o instanceof Function) && name.equals(((Function) o).name);
    }

    public String toString() {
	return "Function{name='" + name + "', args=" + nargs + ", locals=" + nlocals + ", address=" + address + "}";
    }
}
