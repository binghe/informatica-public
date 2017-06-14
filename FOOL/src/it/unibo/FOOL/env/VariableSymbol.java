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

public class VariableSymbol extends Symbol {
    int id; // the ID of symbol is used by assembler
    boolean polyp; // Polymorphic type?
    boolean initp; // initialized?

    // @formatter:off
    public VariableSymbol(String name, Type type) { super(name, type); }
    public int getID() { return id; }
    public void setPoly(boolean b) { polyp = b; }
    public boolean polyp() { return polyp; }
    public void setInit(boolean b) { initp = b; }
    public boolean initp() { return initp; }
}
