/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 * 
 * Type analysis phase
 */

package it.unibo.FOOL;

import java.util.*;
import java.util.Map.*;
import org.antlr.v4.runtime.tree.*;
import it.unibo.FOOL.FOOLParser.*;
import it.unibo.FOOL.env.*;

public class TypePhase extends FOOLBaseListener {
	ParseTreeProperty<Scope> scopes;
	GlobalScope globals;
	Scope currentScope;
	FOOLParser parser;

	// type annotations to the parsing tree:
	ParseTreeProperty<Type> types = new ParseTreeProperty<Type>();
	Type tINT;
	Type tBOOL;

	public TypePhase(DefPhase ref, FOOLParser parser) {
		scopes = ref.scopes;
		globals = ref.globals;
		currentScope = globals;
		this.parser = parser;
		initializeTypeSystem();
	}

	public void initializeTypeSystem() {
		tBOOL = getType("bool");
		tINT = getType("int");
	}

	public Type getType(String name) {
		Symbol sym = globals.resolve(name);
		if (sym instanceof BuiltInTypeSymbol)
			return (Type) sym;
		else
			return null;
	}

	public Type getType(ParseTree ctx) { return types.get(ctx); }
	public Type getType(ParseTree ctx, String name) {
		Symbol sym = currentScope.resolve(name);
		if (sym != null)
			return sym.getType();
		else
			return null;
	}

	public void saveType(ParseTree ctx, Type typ) { types.put(ctx, typ); }

	// prog : block SEMIC ;
	public void exitProg(FOOLParser.ProgContext ctx) {
		List<BlockContext> blocks = ctx.block();
		int n = blocks.size();
		// the type of entire prog is the type of the last block
		Type prog = getType(blocks.get(n-1));
		saveType(ctx, prog);
		System.out.println("type of prog is: " + prog);
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

	// exp : left=term (PLUS right=exp)?
	public void exitExp(FOOLParser.ExpContext ctx) {
		Type left = getType(ctx.left);
		Type right = getType(ctx.right);
		if (right == null)
			saveType(ctx, left);
		else if (left == tINT && right == tINT)
			saveType(ctx, tINT);
		else
			System.err.println("type mismatch in Exp: " + ctx.toStringTree(parser));
	}

	// term : left=factor (TIMES right=term)?
	public void exitTerm(FOOLParser.TermContext ctx) {
		Type left = getType(ctx.left);
		Type right = getType(ctx.right);
		if (right == null)
			saveType(ctx, left);
		else if (left == tINT && right == tINT)
			saveType(ctx, tINT);
		else
			System.err.println("type mismatch in Term: " + ctx.toStringTree(parser));
	}

	// factor : left=value (EQ right=value)?
	public void exitFactor(FOOLParser.FactorContext ctx) {
		Type left = getType(ctx.left);
		Type right = getType(ctx.right);
		if (right == null)
			saveType(ctx, left);
		else if (left == right)
			saveType(ctx, tBOOL);
		else
			System.err.println("type mismatch in Factor: " + ctx.toStringTree(parser));
	}

	// INTEGER
	public void exitIntVal(FOOLParser.IntValContext ctx) { saveType(ctx, tINT); }

	// ( TRUE | FALSE )
	public void exitBoolVal(FOOLParser.BoolValContext ctx) { saveType(ctx, tBOOL); }

	// LPAR exp RPAR
	public void exitBaseExp(FOOLParser.BaseExpContext ctx) { saveType(ctx, getType(ctx.exp())); }

	// IF cond=exp THEN CLPAR thenBranch=exp CRPAR ELSE CLPAR elseBranch=exp CRPAR
	public void exitIfExp(FOOLParser.IfExpContext ctx) {
		Type cond = getType(ctx.cond);
		Type thenBranch = getType(ctx.thenBranch);
		Type elseBranch = getType(ctx.elseBranch);
		if (cond == tBOOL && thenBranch == elseBranch)
			saveType(ctx, thenBranch);
		else
			System.err.println("type mismatch in IfExp: " + ctx.toStringTree(parser));
	}

	// ID
	public void exitVarExp(FOOLParser.VarExpContext ctx) {
		String name = ctx.ID().getText();
		Type typ = getType(ctx, name);
		if (typ == null)
			System.err.println("no type information for variable: " + name);
		else
			saveType(ctx, typ);
	}

	// ID ( LPAR (exp (COMMA exp)* )? RPAR )?
	public void exitFunExp(FOOLParser.FunExpContext ctx) {
		String name = ctx.ID().getText();
		Symbol sym = currentScope.resolve(name);
		if (sym == null)
			System.err.println("no type information for function: " + name);
		else if (!(sym instanceof MethodSymbol))
			System.err.println("type mismatch in FunExp: " + name);
		else {
			MethodSymbol fun = (MethodSymbol) sym;
			Map<String, Symbol> pars = fun.getMembers();
			Iterator<Entry<String, Symbol>> iter = pars.entrySet().iterator();
			List<ExpContext> args = ctx.exp();
			// 1. check cardinality first
			if (pars.size() != args.size())
				System.err.println("mismatch number of args in FunExp: " + name);
			else {
				// 2. check the type of each argument
				int i = 0;
				while (iter.hasNext()) {
					Entry<String, Symbol> entry = iter.next();
					Symbol parSym = entry.getValue();
					Type parType = parSym.getType();
					ExpContext exp = ctx.exp(i++);
					Type argType = getType(exp);
					if (argType != parType) {
						System.err.println("type mismatch of parameters in FunExp: " + name);
						return;
					}
				}
				// 3. save the type of return value 
				Type typ = fun.getType();
				saveType(ctx, typ);
			}
		}
	}
}
