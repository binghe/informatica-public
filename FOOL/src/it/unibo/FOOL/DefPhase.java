/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 * 
 * Symbolic analysis phase
 */

package it.unibo.FOOL;

/***
 * Excerpted from "The Definitive ANTLR 4 Reference",
 * published by The Pragmatic Bookshelf.
 * Copyrights apply to this code. It may not be used to create training material, 
 * courses, books, articles, and the like. Contact us if you are in doubt.
 * We make no guarantees that this code is fit for any purpose. 
 * Visit http://www.pragmaticprogrammer.com/titles/tpantlr2 for more book information.
***/

/*
 * Essentially changed and extended by Chun Tian for FOOL+ language
 */

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

import it.unibo.FOOL.env.*;

public class DefPhase extends FOOLBaseListener {
	ParseTreeProperty<Scope> scopes = new ParseTreeProperty<Scope>();
	GlobalScope globals;
	Scope currentScope; // define symbols in this scope

	public DefPhase() {
		globals = new GlobalScope();
		initializeTypeSystem();
		currentScope = globals;
	}

	public void initializeTypeSystem() {
		globals.define(new BuiltInTypeSymbol("bool", 0));
		globals.define(new BuiltInTypeSymbol("int", 1));
	}

	public Type getType(String name) {
		Symbol sym = globals.resolve(name);
		if (sym instanceof BuiltInTypeSymbol)
			return (Type) sym;
		else
			return null;
	}

	void saveScope(ParseTree ctx, Scope s) { scopes.put(ctx, s); }

	public void enterLetInExp(FOOLParser.LetInExpContext ctx) {
		LocalScope s = new LocalScope(currentScope);
		saveScope(ctx, s);
		// An offset to the IDs of local variables
		if (currentScope.getScopeName() != "global") {
			int next_id = currentScope.getNextID();
			s.setNextID(next_id);
			System.out.println("base ID of " + s + " is " + next_id);
		}
		currentScope = s;
	}

	public void exitLetInExp(FOOLParser.LetInExpContext ctx) {
		System.out.println("locals: " + currentScope);
		int n = currentScope.getNextID(); // next ID in let binding
		currentScope = currentScope.getEnclosingScope();
		// A method needs know the number of locals in its child LET binding
		if (currentScope.getScopeName() != "global") {
			int next_id = currentScope.getNextID(); // next ID in upper function
			MethodSymbol fun = (MethodSymbol)currentScope;
			fun.setLocals(n - next_id);
		}
	}

	public void enterFun(FOOLParser.FunContext ctx) {
		String name = ctx.ID().getText();
		String typeName = ctx.type().getText();
		Type type = getType(typeName);
		if (type != null) {
			MethodSymbol function = new MethodSymbol(name, type, currentScope);
			currentScope.define(function);	// Define function in current scope
			saveScope(ctx, function);		// Push: set function's parent to current
			// An offset to the IDs of local variables
			int next_id = currentScope.getNextID();
			function.setNextID(next_id);
			System.out.println("base ID of " + function + " is " + next_id);
			currentScope = function;
		} else {
			System.err.println("invalid type: " + typeName);
		}
	}

	public void exitFun(FOOLParser.FunContext ctx) {
		System.out.println("defined function: " + currentScope);
		currentScope = currentScope.getEnclosingScope(); // pop scope
	}

	void defineVar(FOOLParser.TypeContext typeCtx, Token nameToken) {
		String typeName = typeCtx.start.getText();
		Type type = getType(typeName);
		if (type != null) {
			VariableSymbol var = new VariableSymbol(nameToken.getText(), type);
			currentScope.define(var); // Define symbol in current scope
		} else {
			System.err.println("invalid type: " + typeName);
		}
	}

	public void exitVardec(FOOLParser.VardecContext ctx) {
		defineVar(ctx.type(), ctx.ID().getSymbol());
	}

	public void exitVarasm(FOOLParser.VarasmContext ctx) {
		System.out.println("defined variable: " + currentScope);
	}
	
	// Move this method to *RefPhase if we need to support forward references
	public void exitVarExp(FOOLParser.VarExpContext ctx) {
		String name = ctx.ID().getSymbol().getText();
		Symbol var = currentScope.resolve(name);
		if (var == null) {
			System.err.println("no such variable: " + name);
		} else if (!(var instanceof VariableSymbol)) {
			System.err.println(name + " is not a variable");
		}
	}

	// Move this method to *RefPhase if we need to support forward references
	public void exitFunExp(FOOLParser.FunExpContext ctx) {
		String name = ctx.ID().getSymbol().getText();
		Symbol fun = currentScope.resolve(name);
		if (fun == null) {
			System.err.println("no such function: " + name);
		} else if (!(fun instanceof MethodSymbol)) {
			System.err.println(name + " is not a function");
		}
	}
}
