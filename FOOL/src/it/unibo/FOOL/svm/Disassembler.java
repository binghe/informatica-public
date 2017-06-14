/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.svm;

/***
 * Excerpted from "Language Implementation Patterns",
 * published by The Pragmatic Bookshelf.
 * Copyrights apply to this code. It may not be used to create training material, 
 * courses, books, articles, and the like. Contact us if you are in doubt.
 * We make no guarantees that this code is fit for any purpose. 
 * Visit http://www.pragmaticprogrammer.com/titles/tpdsl for more book information.
***/

import java.util.*;

/*
 * Modified by Chun Tian to support display of functions and labels
 */

public class Disassembler {
    byte[] code;
    int codeSize;
    int dataSize;
    protected Object[] constPool;
    private Map<Integer, String> labels = null;
    private Map<Integer, Function> functions = new HashMap<Integer, Function>();
    Bytecode def;
    boolean verbose = true;

    protected Disassembler(byte[] code, int codeSize, int dataSize, Object[] constPool) {
	this.code = code;
	this.codeSize = codeSize;
	this.dataSize = dataSize;
	this.constPool = constPool;
	buildFunctionMap();
    }

    public Disassembler(Assembler assem) {
	this.code = assem.getMachineCode();
	this.codeSize = assem.getCodeMemorySize();
	this.dataSize = assem.getDataSize();
	this.constPool = assem.getConstantPool();
	buildFunctionMap();
	// initialize labels
	labels = new HashMap<Integer, String>();
	for (Label l : assem.getLabels())
	    labels.put(l.address, l.name);
    }

    private void buildFunctionMap() {
	for (Object c : constPool)
	    if (c instanceof Function) {
		Function f = (Function) c;
		functions.put(f.address, f);
	    }
    }

    public void disassemble() {
	System.out.println("Disassembly:");
	System.out.println(".global " + dataSize);
	int i = 0;
	while (i < codeSize) {
	    i = disassembleInstruction(i);
	    System.out.println();
	}
	System.out.println();
    }

    protected int disassembleInstruction(int ip) {
	int opcode = code[ip];
	Bytecode.Instruction I = Bytecode.instructions[opcode];
	String instrName = I.name;
	if (verbose) printLabel(ip); // newly added
	System.out.printf("  %04d:\t%-11s", ip, instrName);
	ip++;
	if (I.n == 0) {
	    System.out.print("  "); /* 2 spaces */
	    return ip;
	}
	List<String> operands = new ArrayList<String>();
	for (int i = 0; i < I.n; i++) {
	    int operand = Assembler.getInt(code, ip);
	    ip += 4;
	    switch (I.type[i]) {
	    case Bytecode.REG:
		operands.add("r" + operand);
		break;
	    case Bytecode.FUNC:
	    case Bytecode.POOL:
		operands.add(showConstPoolOperand(operand));
		break;
	    case Bytecode.LABEL:
		operands.add(showLabel(operand));
		break;
	    case Bytecode.INT:
		operands.add(String.valueOf(operand));
		break;
	    }
	}
	for (int i = 0; i < operands.size(); i++) {
	    String s = (String) operands.get(i);
	    if (i > 0) System.out.print(", ");
	    System.out.print(s);
	}
	return ip;
    }

    private String showConstPoolOperand(int poolIndex) {
	StringBuilder buf = new StringBuilder();
	buf.append("#");
	buf.append(poolIndex);
	String s = constPool[poolIndex].toString();
	if (constPool[poolIndex] instanceof String)
	    s = '"' + s + '"';
	else if (constPool[poolIndex] instanceof Function) {
	    Function fs = (Function) constPool[poolIndex];
	    s = fs.name + "@" + fs.address;
	}
	buf.append(":");
	buf.append(s);
	return buf.toString();
    }

    private String showLabel(int address) {
	StringBuilder buf = new StringBuilder();
	buf.append(address);
	if (labels != null) {
	    String label = labels.get(address);
	    buf.append(" [" + label + "]");
	}
	return buf.toString();
    }

    private void printLabel(int address) {
	Function f = functions.get(address);
	if (f != null) {
	    System.out.printf(".%s nargs=%d nlocals=%d\n", f.name, f.nargs, f.nlocals);
	}
	if (labels != null) {
	    String label = labels.get(address);
	    if (label != null) {
		System.out.printf("%s:\n", label);
	    }
	}
    }
}
