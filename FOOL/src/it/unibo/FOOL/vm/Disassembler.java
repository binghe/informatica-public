/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.vm;

/***
 * Excerpted from "Language Implementation Patterns",
 * published by The Pragmatic Bookshelf.
 * Copyrights apply to this code. It may not be used to create training material, 
 * courses, books, articles, and the like. Contact us if you are in doubt.
 * We make no guarantees that this code is fit for any purpose. 
 * Visit http://www.pragmaticprogrammer.com/titles/tpdsl for more book information.
***/

import java.util.*;

public class Disassembler {
	byte[] code;
    int codeSize;
    int dataSize;
    protected Object[] constPool;
    Bytecode def;

    protected Disassembler(byte[] code, int codeSize, int dataSize, Object[] constPool) {
        this.code = code;
        this.codeSize = codeSize;
        this.dataSize = dataSize;
        this.constPool = constPool;
    }

    public Disassembler(Assembler assem) {
    	this.code = assem.getMachineCode();
    	this.codeSize = assem.getCodeMemorySize();
    	this.dataSize = assem.getDataSize();
    	this.constPool = assem.getConstantPool();
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
        System.out.printf("%04d:\t%-11s", ip, instrName);
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
                case Bytecode.FUNC:
                case Bytecode.POOL:
                    operands.add(showConstPoolOperand(operand));
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
            Function fs = (Function)constPool[poolIndex];
            s = fs.name + "()@" + fs.address;
        }
        buf.append(":");
        buf.append(s);
        return buf.toString();
    }
}
