/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL;

/**
 * Symbolic analysis (phase 2 of 2)
 */

import org.antlr.v4.runtime.tree.*;
import it.unibo.FOOL.env.*;

// forward reference handler
public class RefPhase extends FOOLBaseListener {
    ParseTreeProperty<Scope> scopes;
    GlobalScope globals;
    Scope currentScope;
    ClassSymbol currentClass;
    boolean on_error = false;

    public RefPhase(DefPhase def) {
	this.globals = def.globals;
	this.scopes = def.scopes;
	currentScope = globals;
    }

    public Type getType(String name) {
	Symbol sym = globals.resolve(name);
	if (sym instanceof BuiltinTypeSymbol)
	    return (Type) sym;
	else if (sym instanceof ClassSymbol)
	    return (Type) sym;
	else
	    return null;
    }

    public void enterLetInExp(FOOLParser.LetInExpContext ctx) {
	currentScope = scopes.get(ctx);
    }

    public void exitLetInExp(FOOLParser.LetInExpContext ctx) {
	currentScope = currentScope.getEnclosingScope();
    }

    public void exitFunExp(FOOLParser.FunExpContext ctx) {
	String name = ctx.ID().getSymbol().getText();
	Symbol fun = currentScope.resolve(name);
	if (fun == null) {
	    System.err.println("no such function: " + name);
	    on_error = true;
	} else if (!(fun instanceof GenericFunction)) {
	    System.err.println(name + " is not a function");
	    on_error = true;
	}
    }

    /* for detections of uninitialized variables */
    public void exitVarasm(FOOLParser.VarasmContext ctx) {
	String name = ctx.vardec().ID().getText();
	VariableSymbol var;
	// if we're in a class init function, check the class member scope
	if (currentScope.getEnclosingScope() instanceof ClassSymbol) {
	    ClassSymbol cls = (ClassSymbol) currentScope.getEnclosingScope();
	    var = (VariableSymbol) cls.resolveMember(name);
	} else
	    var = (VariableSymbol) currentScope.resolve(name);
	var.setInit(true);
    }

    public void exitVarExp(FOOLParser.VarExpContext ctx) {
	String name = ctx.ID().getText();
	Symbol sym = currentScope.resolve(name);
	if (sym instanceof VariableSymbol) {
	    VariableSymbol var = (VariableSymbol) sym;
	    if (!var.initp()) {
		System.err.println("[exitVarExp] access to uninitialized variable: " + name);
		on_error = true;
	    }
	} else {
	    System.err.println("[exitVarExp] no such variable: " + name);
	    on_error = true;
	}
    }

    // @formatter:off
    public boolean on_error() { return on_error; } // @formatter:on

    /**
     * Below are special code for the object-oriented features (FOOL+)
     */

    public void enterFun(FOOLParser.FunContext ctx) {
	String name = ctx.ID().getText();
	MethodSymbol method = (MethodSymbol) scopes.get(ctx);
	Symbol sym = currentScope.resolve(name);
	// 1. create a generic function for the first occurrence of its methods
	if (sym == null) {
	    GenericFunction gf = new GenericFunction(name, currentScope, method.nargs());
	    System.out.println("created new generic function: " + name);
	    currentScope.define(gf);
	    sym = (Symbol) gf;
	}
	// 2. add the method into the generic function
	if (sym instanceof GenericFunction) {
	    GenericFunction gf = (GenericFunction) sym;
	    String cname = method.getName();
	    boolean flag = gf.addMethod(method);
	    if (flag)
		System.out.println("added new method " + cname + " into generic function " + gf.getName());
	    else {
		System.err.println("[enterFun] error when adding new method into gf");
		on_error = true;
	    }
	} else {
	    System.err.println("[enterFun] non-function symbol detected:" + name);
	    on_error = true;
	}
	// 3. still use method as current scope
	currentScope = scopes.get(ctx);
    }

    public void exitFun(FOOLParser.FunContext ctx) {
	currentScope = currentScope.getEnclosingScope();
    }

    public void enterDefcls(FOOLParser.DefclsContext ctx) {
	String name = ctx.ID().getText();
	ClassSymbol cls = (ClassSymbol) globals.resolve(name);
	MethodSymbol function = cls.initFunction();
	currentScope = function;
	currentClass = cls;
    }

    public void exitDefcls(FOOLParser.DefclsContext ctx) {
	currentScope = globals;
    }
}
