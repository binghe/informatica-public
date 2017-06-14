/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL;

import java.util.*;
import org.antlr.v4.runtime.tree.*;
import it.unibo.FOOL.FOOLParser.*;
import it.unibo.FOOL.env.*;

/**
 * Type analysis phase
 */

public class TypePhase extends FOOLBaseListener {
    ParseTreeProperty<Scope> scopes;
    GlobalScope globals;
    Scope currentScope;
    ClassSymbol currentClass;
    boolean on_error = false;

    // type annotations to the parsing tree:
    ParseTreeProperty<Type> types = new ParseTreeProperty<Type>();
    // polymorphic annotations to the parsing tree
    ParseTreeProperty<Boolean> polys = new ParseTreeProperty<Boolean>();
    Type tINT, tBOOL; // built-in types

    public TypePhase(DefPhase ref) {
	scopes = ref.scopes;
	globals = ref.globals;
	currentScope = globals;
	tBOOL = getType("bool");
	tINT = getType("int");
    }

    protected Type getType(String name) {
	Symbol sym = globals.resolve(name);
	if (sym instanceof BuiltinTypeSymbol || sym instanceof ClassSymbol)
	    return (Type) sym;
	else
	    return null;
    }

    // @formatter:off
    protected Type getType(ParseTree ctx) { return types.get(ctx); }
    protected void saveType(ParseTree ctx, Type typ) { types.put(ctx, typ); }
    protected void setPoly(ParseTree ctx, boolean flag) { polys.put(ctx, flag); }

    // @formatter:on
    protected boolean getPoly(ParseTree ctx) {
	Boolean p = polys.get(ctx);
	return (p != null) ? p : false;
    }

    // prog : block SEMIC ;
    public void exitProg(FOOLParser.ProgContext ctx) {
	List<BlockContext> blocks = ctx.block();
	int n = blocks.size();
	// the type of entire prog is the type of the last block
	Type prog = getType(blocks.get(n - 1));
	saveType(ctx, prog);
	System.out.println("type of prog is: " + prog);
    }

    public void exitFunBody(FOOLParser.CodeBodyContext ctx) {
	Type body = getType(ctx.body());
	saveType(ctx, body);
    }

    public void exitCodeBody(FOOLParser.CodeBodyContext ctx) {
	Type typ = getType(ctx.body());
	saveType(ctx, typ);
    }

    public void exitGlobalVar(FOOLParser.GlobalVarContext ctx) {
	Type typ = getType(ctx.varasm());
	saveType(ctx, typ);
    }

    public void enterFun(FOOLParser.FunContext ctx) {
	currentScope = scopes.get(ctx);
    }

    public void exitFun(FOOLParser.FunContext ctx) {
	currentScope = currentScope.getEnclosingScope();
    }

    // block : exp
    public void exitSingleExp(FOOLParser.SingleExpContext ctx) {
	saveType(ctx, getType(ctx.exp()));
    }

    public void enterLetInExp(FOOLParser.LetInExpContext ctx) {
	currentScope = scopes.get(ctx);
    }

    // block : let exp
    public void exitLetInExp(FOOLParser.LetInExpContext ctx) {
	saveType(ctx, getType(ctx.exp()));
	currentScope = currentScope.getEnclosingScope();
    }

    public void exitVardec(FOOLParser.VardecContext ctx) {
	String name = ctx.type().start.getText();
	Type typ = getType(name);
	if (typ == null) {
	    System.err.println("unknown type or class: " + name);
	    on_error = true;
	}
	saveType(ctx, typ);
    }

    // exp : left=term (PLUS right=exp)?
    public void exitExp(FOOLParser.ExpContext ctx) {
	Type left = getType(ctx.left);
	Type right = getType(ctx.right);
	if (right == null) {
	    // pass type and polymorphic info upwards
	    saveType(ctx, left);
	    boolean flag = getPoly(ctx.left);
	    if (flag) setPoly(ctx, flag);
	} else if (left == tINT && right == tINT)
	    saveType(ctx, tINT);
	else {
	    System.err.println("type mismatch in Exp: " + ctx.getText());
	    on_error = true;
	}
    }

    // term : left=factor (TIMES right=term)?
    public void exitTerm(FOOLParser.TermContext ctx) {
	Type left = getType(ctx.left);
	Type right = getType(ctx.right);
	if (right == null) {
	    // passing type and polymorphic info upwards
	    saveType(ctx, left);
	    setPoly(ctx, getPoly(ctx.left));
	} else if (left == tINT && right == tINT)
	    saveType(ctx, tINT);
	else {
	    System.err.println("type mismatch in Term: " + ctx.getText());
	    on_error = true;
	}
    }

    // factor : left=value (EQ right=value)?
    public void exitFactor(FOOLParser.FactorContext ctx) {
	Type left = getType(ctx.left);
	Type right = getType(ctx.right);
	if (right == null) {
	    // passing type and polymorphic info upwards
	    saveType(ctx, left);
	    setPoly(ctx, getPoly(ctx.left));
	} else if (left == right)
	    saveType(ctx, tBOOL);
	else {
	    System.err.println("type mismatch in Factor: " + ctx.getText());
	    on_error = true;
	}
    }

    // value : INTEGER
    public void exitIntVal(FOOLParser.IntValContext ctx) {
	saveType(ctx, tINT);
    }

    // value : ( TRUE | FALSE )
    public void exitBoolVal(FOOLParser.BoolValContext ctx) {
	saveType(ctx, tBOOL);
    }

    // value : LPAR exp RPAR
    public void exitBaseExp(FOOLParser.BaseExpContext ctx) {
	saveType(ctx, getType(ctx.exp()));
	setPoly(ctx, getPoly(ctx.exp()));
    }

    // value : IF cond=exp THEN CLPAR thenBranch=exp CRPAR ELSE CLPAR
    // elseBranch=exp CRPAR
    public void exitIfExp(FOOLParser.IfExpContext ctx) {
	Type cond = getType(ctx.cond);
	Type thenBranch = getType(ctx.thenBranch);
	Type elseBranch = getType(ctx.elseBranch);
	if (cond != tBOOL) {
	    System.err.println("[exitIfExp] the condition is not of type boolean.");
	    on_error = true;
	    return;
	}
	if (thenBranch == elseBranch)
	    saveType(ctx, thenBranch);
	else if (thenBranch.canAssignTo(elseBranch)) {
	    // thenBranch is more specific, choose the other
	    saveType(ctx, elseBranch);
	    setPoly(ctx, true);
	} else if (elseBranch.canAssignTo(thenBranch)) {
	    // elseBranch is more specific, choose the other
	    saveType(ctx, thenBranch);
	    setPoly(ctx, true);
	} else { // two irrelevant types
	    System.err.println("[exitIfExp] type mismatch in IfExp: " + ctx.getText());
	    on_error = true;
	}
    }

    // value : ID
    public void exitVarExp(FOOLParser.VarExpContext ctx) {
	String name = ctx.ID().getText();
	VariableSymbol var = (VariableSymbol) currentScope.resolve(name);
	Type typ = var.getType();
	if (typ == null) {
	    System.err.println("[exitVarExp] no type information for variable: " + name);
	    on_error = true;
	}
	saveType(ctx, typ);
	setPoly(ctx, var.polyp());
    }

    public void exitPrintExp(FOOLParser.PrintExpContext ctx) {
	saveType(ctx, getType(ctx.exp()));
	setPoly(ctx, getPoly(ctx.exp()));
    }

    // @formatter:off
    public boolean on_error() { return on_error; } // @formatter:on

    /**
     * Below are special code for the object-oriented features (FOOL+)
     */

    public void exitClassDef(FOOLParser.ClassDefContext ctx) {
	saveType(ctx, (Type) currentClass);
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
	saveType(ctx, (Type) currentClass);
    }

    public void exitClassExp(FOOLParser.ClassExpContext ctx) {
	String name = ctx.ID().getText();
	Symbol sym = globals.resolve(name);
	if (sym instanceof ClassSymbol)
	    saveType(ctx, (Type) sym);
	else {
	    System.err.println("unknown class: " + name);
	    on_error = true;
	}
    }

    public void exitSlotExp(FOOLParser.SlotExpContext ctx) {
	ValueContext v = ctx.value();
	TerminalNode s = ctx.ID();
	String object = v.getText();
	String slot = s.getText();

	Type varTyp = getType(v);
	if (!(varTyp instanceof ClassSymbol)) {
	    System.err.println("[exitSlotExp] The type of " + object + " is not class");
	    on_error = true;
	}
	ClassSymbol cls = (ClassSymbol) varTyp;
	VariableSymbol var = (VariableSymbol) cls.resolveMember(slot);
	Type typ = var.getType();
	saveType(ctx, typ);
	if (!var.initp()) {
	    System.err.println("[exitVarExp] access to uninitialized slot: " + slot);
	    on_error = true;
	}
    }

    public void exitMethodExp(FOOLParser.MethodExpContext ctx) {
	ValueContext object = ctx.value();
	TerminalNode method = ctx.ID();

	String name = method.getText();
	Symbol sym = currentScope.resolve(name);
	if (sym instanceof GenericFunction) {
	    GenericFunction gf = (GenericFunction) sym;
	    List<ExpContext> args = ctx.exp();
	    List<Type> argTypes = new ArrayList<Type>();
	    argTypes.add(getType(object));
	    argTypes.addAll(getTypes(args));
	    MethodSymbol fun = gf.findMethod(argTypes);
	    if (fun == null) {
		System.err.println("[exitMethodExp] no applicable method for gf: " + name);
		on_error = true;
	    }

	    Type typ = fun.getType();
	    saveType(ctx, typ);
	    // the method call is polymorphic if the object and arg is so
	    boolean poly = getPoly(object);
	    for (ExpContext e : args)
		if (getPoly(e)) poly = true;
	    setPoly(ctx, poly);
	    if (poly) {
		System.out.println("set method call as polymorphic: " + ctx.getText());
	    }
	} else {
	    System.err.println("[exitMethodExp] functor is not a method: " + sym.getName());
	    on_error = true;
	}
    }

    public List<Type> getTypes(List<ExpContext> args) {
	Iterator<ExpContext> iter = args.iterator();
	List<Type> argTypes = new LinkedList<Type>();
	while (iter.hasNext()) {
	    ExpContext exp = iter.next();
	    argTypes.add(getType(exp));
	}
	return argTypes;
    }

    // value : ID ( LPAR (exp (COMMA exp)* )? RPAR )?
    public void exitFunExp(FOOLParser.FunExpContext ctx) {
	String name = ctx.ID().getText();
	Symbol sym = currentScope.resolve(name);
	if (sym == null) {
	    System.err.println("no type information for function: " + name);
	    on_error = true;
	    return;
	} else if (!(sym instanceof GenericFunction)) {
	    System.err.println("non-function symbol used as functor: " + name);
	    on_error = true;
	    return;
	}

	List<ExpContext> args = ctx.exp();
	GenericFunction gf = (GenericFunction) sym;
	// 1. check cardinality first
	if (gf.nargs() != args.size()) {
	    System.err.println("mismatch number of args in FunExp: " + name);
	    on_error = true;
	    return;
	}

	// 2. find effective method
	List<Type> argTypes = this.getTypes(args);
	MethodSymbol fun = gf.findMethod(argTypes);
	if (fun == null) {
	    System.err.println("no applicable method for gf: " + name);
	    on_error = true;
	    return;
	}

	// 3. save the type of return value
	Type typ = fun.getType();
	saveType(ctx, typ);

	// 4. the funcall is polymorphic if any arg is so
	boolean poly = false;
	for (ExpContext e : args)
	    if (getPoly(e)) poly = true;
	if (poly) {
	    setPoly(ctx, poly);
	    System.out.println("set funcall call as polymorphic: " + ctx.getText());
	}
    }

    public void exitVarasm(FOOLParser.VarasmContext ctx) {
	ParseTree lhs = ctx.vardec();
	ParseTree rhs = ctx.exp();
	Type lhsType = getType(lhs);
	Type rhsType = getType(rhs);
	if (rhsType.canAssignTo(lhsType)) { // rhs is more specific
	    saveType(ctx, lhsType);
	    // Variable assignment is the beginning of Polymorphic types, such
	    // information will pass upwards and be contagious to upper nodes
	    // and also variable symbols.
	    boolean flag = getPoly(rhs);
	    if (lhsType != rhsType || flag) {
		setPoly(ctx, true);
		String name = ctx.vardec().ID().getText();
		VariableSymbol var = (VariableSymbol) currentScope.resolve(name);
		var.setPoly(true);
		System.out.println("The type of " + name + " is polymorphic!");
	    }
	} else {
	    System.err.println("type mismatch in var assignment: " + rhsType + " to " + lhsType);
	    on_error = true;
	}
    }
}
