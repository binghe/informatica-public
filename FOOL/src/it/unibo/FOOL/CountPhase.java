/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 * 
 * A native way for counting nodes and terminals in ANTLR's parsing tree 
 */

package it.unibo.FOOL;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

public final class CountPhase extends FOOLBaseListener {
	int nodes = 0;
	int terms = 0;
	
	public int getNodes() { return nodes; }
	public int getTerms() { return terms; }

	public void enterEveryRule(ParserRuleContext ctx) { nodes++; }
	public void visitTerminal(TerminalNode node) { terms++; }
}
