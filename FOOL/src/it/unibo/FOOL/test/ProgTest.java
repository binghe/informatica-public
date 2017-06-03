/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Unit test framework for simple programs defined in strings
 */

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

import it.unibo.FOOL.*;
import it.unibo.FOOL.vm.*;

public abstract class ProgTest {
	protected static String prog;
	protected static boolean trace = false;
	protected static Assembler assem;

	public static void compile() {
		CharStream input = CharStreams.fromString(prog);
		FOOLLexer lexer = new FOOLLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		FOOLParser parser = new FOOLParser(tokens);
		parser.setErrorHandler(new ErrorStrategy());
		ParseTree tree = parser.prog();
		ParseTreeWalker walker = new ParseTreeWalker();

		System.out.println("0. original code:");
		System.out.println(prog);

		System.out.println("3. Symbol Analysis:");
		DefPhase def = new DefPhase();
		walker.walk(def, tree);
		System.out.println(" done.");

		System.out.println("4. Type Analysis:");
		TypePhase typ = new TypePhase(def, parser);
		walker.walk(typ, tree);

		System.out.println("5. Emit Bytecode:");
		EmitPhase emit = new EmitPhase(typ);
		emit.visit(tree);
		System.out.println(" done.");

		System.out.println("6. Disassemble Bytecode:");
		assem = emit.getAssembly();
	    Disassembler disasm = new Disassembler(assem);
	    disasm.disassemble();
	}

	public static void run() {
		compile();
	    System.out.println("7. Run Bytecode:");
	    Interpreter vm = new Interpreter(assem);
	    vm.setTrace(trace);
	    try {
			vm.exec();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
