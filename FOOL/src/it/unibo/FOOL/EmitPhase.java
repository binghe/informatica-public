/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 * 
 * Code generation phase
 */

package it.unibo.FOOL;

import org.antlr.v4.runtime.tree.*;
import it.unibo.FOOL.env.*;
import it.unibo.FOOL.vm.*;

public class EmitPhase extends FOOLBaseVisitor<ParseTree> {
	ParseTreeProperty<Scope> scopes;
	ParseTreeProperty<Type> types;
	GlobalScope globals;
	Scope currentScope;
	Assembler assem;
	int dataSize = 0;
	int top_locals = 0; // for top-level let binding

	public EmitPhase(TypePhase typ) {
		scopes = typ.scopes;
		types = typ.types;
		globals = typ.globals;
		currentScope = globals;
		assem = new Assembler();
	}

	public Assembler getAssembly() { return assem; }
	public Type getType(ParseTree ctx) { return types.get(ctx); }

	public ParseTree visitProg(FOOLParser.ProgContext ctx) {
		ParseTree body = visitChildren(ctx);
		assem.gen("halt");
		assem.defineDataSize(dataSize);
		assem.setLocals(top_locals);
		assem.check();
		return body;
	}

	public ParseTree visitLetInExp(FOOLParser.LetInExpContext ctx) {
		currentScope = scopes.get(ctx);
		ParseTree body = visitChildren(ctx);
		Scope s = currentScope.getEnclosingScope();
		// special treatment for top-level LET binding
		if (s.getScopeName() == "global") {
			// if there're multiple top-level LET bindings, we want the maximal one
			top_locals = Math.max(top_locals, currentScope.getNextID());
			System.out.println("nlocals for top-level LET: " + top_locals);
		}
		currentScope = s;
		return body;
	}

	public ParseTree visitIntVal(FOOLParser.IntValContext ctx) {
		ParseTree body = visitChildren(ctx);
		int i = Integer.valueOf(ctx.getText());
		assem.gen("iconst", i);
		return body;
	}

	public ParseTree visitBoolVal(FOOLParser.BoolValContext ctx) {
		ParseTree body = visitChildren(ctx);
		String text = ctx.getText();
		if (text.equals("true"))
			assem.gen("iconst", 1);
		else
			assem.gen("null");
		return body;
	}

	public ParseTree visitPrintExp(FOOLParser.PrintExpContext ctx) {
		ParseTree body = visitChildren(ctx);
		assem.gen("print");
		return body;
	}

	public ParseTree visitFactor(FOOLParser.FactorContext ctx) {
		ParseTree body = visitChildren(ctx);
		Type right = getType(ctx.right);
		if (right != null) assem.gen("ieq");
		return body;
	}

	public ParseTree visitTerm(FOOLParser.TermContext ctx) {
		ParseTree body = visitChildren(ctx);
		Type right = getType(ctx.right);
		if (right != null) assem.gen("imul");
		return body;
	}

	public ParseTree visitExp(FOOLParser.ExpContext ctx) {
		ParseTree body = visitChildren(ctx);
		Type right = getType(ctx.right);
		if (right != null) assem.gen("iadd");
		return body;
	}
	
	public ParseTree visitIfExp(FOOLParser.IfExpContext ctx) {
		Label L1 = assem.newLabel("else");
		Label L2 = assem.newLabel("endif");
		visit(ctx.cond);		// gen(cond)
		assem.gen("null");		// push 0 (false)
		assem.gen("ieq");		// test if cond is true
		assem.gen("brt", L1);	// if not, go to L1 (else)
		visit(ctx.thenBranch);	//   gen(then)
		assem.gen("br", L2);	// goto L2 (endif)
		assem.setLabel(L1);		// else:
		visit(ctx.elseBranch);	// 	 gen(else)
		assem.setLabel(L2);		// endif:
		return ctx;
	}

	/* Code generation of variable definitions */
	public ParseTree visitVarasm(FOOLParser.VarasmContext ctx) {
		String name = ctx.vardec().ID().getText();
		Symbol sym = currentScope.resolve(name);
		assert(sym != null);

		String op;
		if (currentScope.getScopeName() == "global") {
			op = "gstore";
			dataSize++;
		} else
			op = "store";

		int index = sym.getID();
		visit(ctx.exp());
		assem.gen(op, index);
		return ctx;
	}

	/* Code generation of variable references */
	public ParseTree visitVarExp(FOOLParser.VarExpContext ctx) {
		String name = ctx.ID().getText();
		Symbol sym = currentScope.resolve(name);
		assert(sym != null);

		String op;
		if (sym.getScope().getScopeName() == "global")
			op = "gload";
		else
			op = "load";

		int index = sym.getID();
		assem.gen(op, index);
		return ctx;
	}

	/* Code generation of function definitions */
	public ParseTree visitFun(FOOLParser.FunContext ctx) {
		currentScope = scopes.get(ctx);
		MethodSymbol fun = (MethodSymbol)currentScope;
		int nargs = fun.getNextID(); // scope args + local args
		int nargs2 = fun.nargs();
		int nargs1 = nargs - nargs2;
		int nlocals = fun.nlocals();

		String name = ctx.ID().getText();
		Label skip = assem.newLabel("skip");
		assem.gen("br", skip); // jump directly to the end of function definition
		assem.defineFunction(name, nargs, nlocals);
		System.out.println("defining function " + name + " [nargs: " + nargs +
				"(" + nargs1 + " + " + nargs2 + "), nlocals: " + nlocals + "]");
		ParseTree body = visit (ctx.block()); // generate function body
		assem.gen("ret");
		assem.setLabel(skip);  // jumped here

		currentScope = currentScope.getEnclosingScope();
		return body;
	}

	/* Code generation of function calls */
	public ParseTree visitFunExp(FOOLParser.FunExpContext ctx) {
		String name = ctx.ID().getText();
		MethodSymbol fun = (MethodSymbol)currentScope.resolve(name);
		int last_id = fun.getNextID();
		int base_id = last_id - fun.nargs();
		
		// 1. push scope arguments
		for (int id = 0; id < base_id; id++)
			assem.gen("load", id);
		// 2. push local arguments
		ParseTree body = visitChildren(ctx);
		// 3. generate function call
		assem.gen("call", new Function(name));
		return body;
	}
}
