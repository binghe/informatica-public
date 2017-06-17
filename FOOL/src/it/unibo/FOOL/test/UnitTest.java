/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import it.unibo.FOOL.*;
import it.unibo.FOOL.svm.*;

/*
 * Unit test framework for simple programs defined in strings
 */

public abstract class UnitTest {
    protected static String prog;
    protected static Object result;
    protected static boolean trace = false;
    protected static boolean tail_rec = true;
    protected static boolean use_indirect = false;
    protected static Assembler assem;

    public static void compile() {
	CharStream input = CharStreams.fromString(prog); // ANTLR 4.7
	FOOLLexer lexer = new FOOLLexer(input);
	CommonTokenStream tokens = new CommonTokenStream(lexer);
	FOOLParser parser = new FOOLParser(tokens);
	parser.setErrorHandler(new ErrorStrategy());
	ParseTree tree = parser.prog();
	ParseTreeWalker walker = new ParseTreeWalker();

	System.out.println("1. original code:");
	System.out.println(prog);

	System.out.println("2. Symbol Analysis:");
	DefPhase def = new DefPhase();
	walker.walk(def, tree);
	if (def.on_error()) throw new RuntimeException("DefPhase failed.");
	RefPhase ref = new RefPhase(def);
	walker.walk(ref, tree);
	if (ref.on_error()) throw new RuntimeException("RefPhase failed.");
	System.out.println(" done.");

	System.out.println("3. Type Analysis:");
	TypePhase typ = new TypePhase(def);
	walker.walk(typ, tree);
	if (typ.on_error()) {
	    throw new RuntimeException("TypPhase failed.");
	}

	System.out.println("4. Emit Bytecode:");
	EmitPhase emit = new EmitPhase(typ);
	assem = emit.getAssembly();
	emit.set_tail_rec(tail_rec);
	assem.useIndirect(use_indirect);
	emit.visit(tree);
	if (emit.on_error()) {
	    throw new RuntimeException("EmitPhase failed.");
	}

	System.out.println("5. Disassemble Bytecode:");
	Disassembler disasm = new Disassembler(assem);
	disasm.disassemble();
    }

    public static Object run() {
	Object top_of_stack = null;
	compile();
	System.out.println("6. Run Bytecode:");
	Interpreter vm = new Interpreter(assem);
	vm.setTrace(trace);
	top_of_stack = vm.exec();
	return top_of_stack;
    }
}
