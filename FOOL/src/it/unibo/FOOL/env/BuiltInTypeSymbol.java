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

public class BuiltInTypeSymbol extends Symbol implements Type {
	int typeIndex;

	public BuiltInTypeSymbol(String name, int typeIndex) {
		super(name);
		this.typeIndex = typeIndex;
	}

	public int getTypeIndex() { return typeIndex; }
	public String toString() { return getName(); }

	public boolean canAssignTo(Type destType) {
		return (this == destType);
	}
}
