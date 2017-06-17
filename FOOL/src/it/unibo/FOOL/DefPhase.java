/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import it.unibo.FOOL.env.*;

/**
 * Symbolic analysis (phase 1 of 2)
 */

public class DefPhase extends FOOLBaseListener {
    ParseTreeProperty<Scope> scopes = new ParseTreeProperty<Scope>();
    GlobalScope globals;
    Scope currentScope; // define symbols in this scope
    ClassSymbol currentClass;
    boolean on_error = false;

    public DefPhase() {
	globals = new GlobalScope();
	initializeTypeSystem();
	currentScope = globals;
    }

    public void initializeTypeSystem() {
	globals.define(new BuiltinTypeSymbol("bool"));
	globals.define(new BuiltinTypeSymbol("int"));
	initializeClassSystem(); // for OO support
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

    void saveScope(ParseTree ctx, Scope s) {
	scopes.put(ctx, s);
    }

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
	    MethodSymbol fun = (MethodSymbol) currentScope;
	    fun.setLocals(n - next_id);
	}
    }

    public void enterFun(FOOLParser.FunContext ctx) {
	String name = ctx.ID().getText();
	String typeName = ctx.type().getText();
	Type type = getType(typeName);
	if (type != null) {
	    MethodSymbol function = new MethodSymbol(name, type, currentScope);
	    saveScope(ctx, function);
	    // offset to the IDs of local variables
	    int next_id = currentScope.getNextID();
	    function.setNextID(next_id);
	    System.out.println("base ID of " + function + " is " + next_id);
	    currentScope = function;
	} else {
	    System.err.println("[enterFun] invalid type: " + typeName + " of function " + name);
	    on_error = true;
	}
    }

    public void exitFun(FOOLParser.FunContext ctx) {
	System.out.println("defined function: " + currentScope);
	currentScope = currentScope.getEnclosingScope(); // pop scope
    }

    public void exitVardec(FOOLParser.VardecContext ctx) {
	defineVar(ctx.type(), ctx.ID().getSymbol());
    }

    public void exitVarExp(FOOLParser.VarExpContext ctx) {
	String name = ctx.ID().getText();
	Scope scope = currentScope;

	// If we're in a class definition, set scope to the init function
	if (scope instanceof ClassSymbol) {
	    scope = ((ClassSymbol) scope).initFunction();
	}

	Symbol var = scope.resolve(name);
	if (var == null) {
	    System.err.println("no such variable: " + name);
	    on_error = true;
	} else if (!(var instanceof VariableSymbol)) {
	    System.err.println(name + " is not a variable");
	    on_error = true;
	}
    }

    // @formatter:off
    public boolean on_error() { return on_error; } // @formatter:on

    /**
     * Below are special code for the object-oriented features (FOOL+)
     */

    public void initializeClassSystem() {
	// the class "null" serves as class "t" in CL
	ClassSymbol top = new ClassSymbol(ClassSymbol.top, globals, null);
	top.setNextID(1); // slot 0 is reserved for holding typeIndex
	globals.define(top);
    }

    public ClassSymbol getClass(String name) {
	Symbol cls = globals.resolve(name);
	if (cls instanceof ClassSymbol)
	    return (ClassSymbol) cls;
	else
	    return null;
    }

    public void enterDefcls(FOOLParser.DefclsContext ctx) {
	assert (currentScope == globals);
	// 1. get parent class
	String parent;
	FOOLParser.SupersContext p = ctx.supers();
	if (p != null)
	    parent = p.ID().getText();
	else
	    parent = ClassSymbol.top;
	ClassSymbol parentClass = getClass(parent);

	// 2. create class symbol
	String name = ctx.ID().getText();
	ClassSymbol cls = new ClassSymbol(name, currentScope, parentClass);
	currentScope.define(cls); // Define class in current scope
	int next_id = parentClass.getNextID();
	cls.setNextID(next_id); // offset of the slots
	System.out.println("base ID of class " + name + " is " + next_id);
	currentClass = cls;
	saveScope(ctx, cls); // attach class symbol to the parse tree

	// 3. create init function symbol, returning the class
	MethodSymbol function = new MethodSymbol(name + "_init", (Type) cls, currentClass);
	function.setNextID(1); // 0 is reserved for the object to initialize
	currentScope.define(function); // Define function in current scope
	cls.setInitFunction(function); // attach init function to class symbol

	MethodSymbol newFun = new MethodSymbol(name + "_new", (Type) cls, currentClass);
	newFun.setNextID(1); // 0 is reserved for the object to initialize
	currentScope.define(newFun); // Define function in current scope
	cls.setNewFunction(newFun);

	// 4. ready to receive parameters for init function
	currentScope = function;
    }

    public void enterSlots(FOOLParser.SlotsContext ctx) {
	currentScope = currentClass; // ready to receive class slots
    }

    public void exitSlots(FOOLParser.SlotsContext ctx) {
	System.out.println("defined class: " + currentScope);
	currentScope = currentClass.initFunction();
    }

    public void exitDefcls(FOOLParser.DefclsContext ctx) {
	MethodSymbol init = currentClass.initFunction();
	MethodSymbol nf = currentClass.newFunction();
	nf.setNextID(init.getNextID());
	System.out.println("defined init function: " + currentScope);
	currentScope = globals;
    }

    void defineVar(FOOLParser.TypeContext typeCtx, Token nameToken) {
	String name = nameToken.getText();
	String typeName = typeCtx.start.getText();
	Type type = getType(typeName);
	if (type != null) {
	    Symbol other = currentScope.resolve(name);
	    if (other != null && currentScope == other.getScope()) {
		System.err.println("[defineVar] Duplicated variables found in current scope: " + name);
		on_error = true;
		return;
	    } else if (currentScope instanceof ClassSymbol) {
		ClassSymbol cls = (ClassSymbol) currentScope;
		other = cls.resolveMember(name);
		if (other != null && currentScope == other.getScope()) {
		    System.err.println("[defineVar] Duplicated slots found in current class: " + name);
		    on_error = true;
		    return;
		} else if (other != null && currentScope != other.getScope()) {
		    System.out.println("overloading parent slot: " + name);
		    return;
		}
	    }
	    VariableSymbol var = new VariableSymbol(name, type);
	    currentScope.define(var); // Define symbol in current scope
	    System.out.println("defined slot/variable " + name + " in " + currentScope);
	    if (currentScope instanceof MethodSymbol) {
		// disable initialization check for function parameters
		var.setInit(true);
	    }
	} else {
	    System.err.println("[defineVar] invalid type: " + typeName + " of variable " + name);
	    on_error = true;
	}
    }
}
