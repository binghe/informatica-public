/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 * 
 * Entry class
 */

package it.unibo.FOOL;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

import it.unibo.FOOL.vm.*;

public final class Main {
	public static void main(String[] args) throws Exception {
		CharStream input = null;
		if (args.length > 0)
			input = CharStreams.fromFileName(args[0]); // ANTLR 4.7+
		else
			input = CharStreams.fromStream(System.in); // ANTLR 4.7+

		FOOLLexer lexer = new FOOLLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		FOOLParser parser = new FOOLParser(tokens);
		parser.setErrorHandler(new ErrorStrategy());

		ParseTree tree = parser.prog();
		ParseTreeWalker walker = new ParseTreeWalker();

		System.out.println("1. LISP-style parsing tree:");
		System.out.println(tree.toStringTree(parser));

		System.out.println("2. Count nodes and terminals:");
		CountPhase count = new CountPhase();
		walker.walk(count, tree);
		System.out.println("number of nodes: " + count.nodes);
		System.out.println("number of terminals: " + count.terms);

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
		Assembler assem = emit.getAssembly();
	    Disassembler disasm = new Disassembler(assem);
	    disasm.disassemble();

	    System.out.println("7. Run Bytecode:");
		Interpreter vm = new Interpreter(assem);
		vm.setTrace(true);
	    try {
			vm.exec();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
