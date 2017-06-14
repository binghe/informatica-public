/**
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.plus;

import static org.junit.Assert.assertEquals;
import org.junit.Test;
import it.unibo.FOOL.test.*;

/*
 * Method Test #4: classic multimethods
 */
public final class MethodTest4 extends UnitTest {
    @Test
    public void testMethod4() {
	prog = "   class A = object end;				\n"
		+ "class B = object inherit A; end;			\n"
		+ "let int foo(A o1, A o2) 1;				\n"
		+ "    int foo(A o1, B o2) 2;				\n"
		+ "    int foo(B o1, A o2) 3;				\n"
		+ "    int foo(B o1, B o2) 4;				\n"
		+ "    A obj = new A();					\n"
		+ "in obj.foo(obj);					\n";
	result = 1;
	trace = true;
	assertEquals(run(), result);
    }
}

/** @formatter:off
1. original code:
   class A = object end;				
class B = object inherit A; end;			
let int foo(A o1, A o2) 1;				
    int foo(A o1, B o2) 2;				
    int foo(B o1, A o2) 3;				
    int foo(B o1, B o2) 4;				
    A obj = new A();					
in obj.foo(obj);					

2. Symbol Analysis:
base ID of class A is 1
defined class: class A(standard_object):{}
defined init function: <global.A_init():class A(standard_object):{}>
base ID of class B is 1
defined class: class B(A):{}
defined init function: <global.B_init():class B(A):{}>
base ID of <foo():int> is 0
defined variable o1 in <foo(A):int>
defined variable o2 in <foo(A,A):int>
defined function: <foo(A,A):int>
base ID of <foo():int> is 0
defined variable o1 in <foo(A):int>
defined variable o2 in <foo(A,B):int>
defined function: <foo(A,B):int>
base ID of <foo():int> is 0
defined variable o1 in <foo(B):int>
defined variable o2 in <foo(B,A):int>
defined function: <foo(B,A):int>
base ID of <foo():int> is 0
defined variable o1 in <foo(B):int>
defined variable o2 in <foo(B,B):int>
defined function: <foo(B,B):int>
defined variable obj in [obj]
locals: [obj]
created new generic function: foo
added new method foo(A,A) into generic function foo
added new method foo(A,B) into generic function foo
added new method foo(B,A) into generic function foo
added new method foo(B,B) into generic function foo
 done.
3. Type Analysis:
type of prog is: null
4. Emit Bytecode:
defining function foo(A,A) [nargs: 2(0+2), nlocals: 0]
defining function foo(A,B) [nargs: 2(0+2), nlocals: 0]
defining function foo(B,A) [nargs: 2(0+2), nlocals: 0]
defining function foo(B,B) [nargs: 2(0+2), nlocals: 0]
nlocals for top-level LET: 1
defining gf foo [nargs: 2, nlocals: 11]
 done.
5. Disassemble Bytecode:
Disassembly:
.global 0
  0000:	br         88 [end_of_def]
  0005:	ret          
  0006:	struct     3
  0011:	store      1
  0016:	iconst     101
  0021:	load       1
  0026:	fstore     0
  0031:	iconst     100
  0036:	load       1
  0041:	fstore     1
  0046:	null         
  0047:	load       1
  0052:	fstore     2
  0057:	load       1
  0062:	load       0
  0067:	fstore     0
  0072:	load       0
  0077:	call       #0:A_init()@5
  0082:	load       0
  0087:	ret          
  0088:	br         201 [end_of_def']
  0093:	load       0
  0098:	call       #0:A_init()@5
  0103:	ret          
  0104:	struct     4
  0109:	store      1
  0114:	iconst     102
  0119:	load       1
  0124:	fstore     0
  0129:	iconst     101
  0134:	load       1
  0139:	fstore     1
  0144:	iconst     100
  0149:	load       1
  0154:	fstore     2
  0159:	null         
  0160:	load       1
  0165:	fstore     3
  0170:	load       1
  0175:	load       0
  0180:	fstore     0
  0185:	load       0
  0190:	call       #2:B_init()@93
  0195:	load       0
  0200:	ret          
  0201:	br         212 [end_foo(A,A)]
  0206:	iconst     1
  0211:	ret          
  0212:	br         223 [end_foo(A,B)]
  0217:	iconst     2
  0222:	ret          
  0223:	br         234 [end_foo(B,A)]
  0228:	iconst     3
  0233:	ret          
  0234:	br         245 [end_foo(B,B)]
  0239:	iconst     4
  0244:	ret          
  0245:	struct     1
  0250:	call       #1:A_new()@6
  0255:	store      0
  0260:	load       0
  0265:	load       0
  0270:	call       #4:foo(A,A)@206
  0275:	halt         
  0276:	iconst     0
  0281:	store      2
  0286:	iconst     0
  0291:	store      3
  0296:	load       1
  0301:	fload      0
  0306:	store      4
  0311:	load       0
  0316:	load       2
  0321:	dfload       
  0322:	load       3
  0327:	ieq          
  0328:	brt        386 [fail]
  0333:	load       0
  0338:	load       2
  0343:	dfload       
  0344:	load       4
  0349:	ieq          
  0350:	brt        376 [success]
  0355:	load       2
  0360:	iconst     1
  0365:	iadd         
  0366:	store      2
  0371:	br         311 [restart]
  0376:	iconst     1
  0381:	br         387 [end_subclassp]
  0386:	null         
  0387:	ret          
  0388:	load       0
  0393:	fload      0
  0398:	fload      1
  0403:	null         
  0404:	ieq          
  0405:	brt        420 [unbox]
  0410:	load       0
  0415:	br         435 [end_of_fun]
  0420:	load       0
  0425:	fload      1
  0430:	br         435 [end_of_fun]
  0435:	ret          
  0436:	load       0
  0441:	fload      0
  0446:	store      2
  0451:	load       1
  0456:	fload      0
  0461:	store      3
  0466:	struct     4
  0471:	store      4
  0476:	iconst     102
  0481:	load       4
  0486:	fstore     0
  0491:	iconst     101
  0496:	load       4
  0501:	fstore     1
  0506:	iconst     100
  0511:	load       4
  0516:	fstore     2
  0521:	null         
  0522:	load       4
  0527:	fstore     3
  0532:	struct     4
  0537:	store      5
  0542:	iconst     102
  0547:	load       5
  0552:	fstore     0
  0557:	iconst     101
  0562:	load       5
  0567:	fstore     1
  0572:	iconst     100
  0577:	load       5
  0582:	fstore     2
  0587:	null         
  0588:	load       5
  0593:	fstore     3
  0598:	struct     4
  0603:	store      6
  0608:	iconst     102
  0613:	load       6
  0618:	fstore     0
  0623:	iconst     101
  0628:	load       6
  0633:	fstore     1
  0638:	iconst     100
  0643:	load       6
  0648:	fstore     2
  0653:	null         
  0654:	load       6
  0659:	fstore     3
  0664:	struct     3
  0669:	store      7
  0674:	iconst     101
  0679:	load       7
  0684:	fstore     0
  0689:	iconst     100
  0694:	load       7
  0699:	fstore     1
  0704:	null         
  0705:	load       7
  0710:	fstore     2
  0715:	struct     3
  0720:	store      8
  0725:	iconst     101
  0730:	load       8
  0735:	fstore     0
  0740:	iconst     100
  0745:	load       8
  0750:	fstore     1
  0755:	null         
  0756:	load       8
  0761:	fstore     2
  0766:	struct     4
  0771:	store      9
  0776:	iconst     102
  0781:	load       9
  0786:	fstore     0
  0791:	iconst     101
  0796:	load       9
  0801:	fstore     1
  0806:	iconst     100
  0811:	load       9
  0816:	fstore     2
  0821:	null         
  0822:	load       9
  0827:	fstore     3
  0832:	struct     3
  0837:	store      10
  0842:	iconst     101
  0847:	load       10
  0852:	fstore     0
  0857:	iconst     100
  0862:	load       10
  0867:	fstore     1
  0872:	null         
  0873:	load       10
  0878:	fstore     2
  0883:	struct     3
  0888:	store      11
  0893:	iconst     101
  0898:	load       11
  0903:	fstore     0
  0908:	iconst     100
  0913:	load       11
  0918:	fstore     1
  0923:	null         
  0924:	load       11
  0929:	fstore     2
  0934:	load       2
  0939:	load       4
  0944:	call       #8:_subclassp@276
  0949:	brf        989 [next_method_0]
  0954:	load       2
  0959:	load       5
  0964:	call       #8:_subclassp@276
  0969:	brf        989 [next_method_0]
  0974:	pconst     #7:foo(B,B)@239
  0979:	store      12
  0984:	br         1160 [prepare_argument]
  0989:	load       2
  0994:	load       6
  0999:	call       #8:_subclassp@276
  1004:	brf        1044 [next_method_1]
  1009:	load       2
  1014:	load       7
  1019:	call       #8:_subclassp@276
  1024:	brf        1044 [next_method_1]
  1029:	pconst     #6:foo(B,A)@228
  1034:	store      12
  1039:	br         1160 [prepare_argument]
  1044:	load       2
  1049:	load       8
  1054:	call       #8:_subclassp@276
  1059:	brf        1099 [next_method_2]
  1064:	load       2
  1069:	load       9
  1074:	call       #8:_subclassp@276
  1079:	brf        1099 [next_method_2]
  1084:	pconst     #5:foo(A,B)@217
  1089:	store      12
  1094:	br         1160 [prepare_argument]
  1099:	load       2
  1104:	load       10
  1109:	call       #8:_subclassp@276
  1114:	brf        1154 [next_method_3]
  1119:	load       2
  1124:	load       11
  1129:	call       #8:_subclassp@276
  1134:	brf        1154 [next_method_3]
  1139:	pconst     #4:foo(A,A)@206
  1144:	store      12
  1149:	br         1160 [prepare_argument]
  1154:	iconst     -1
  1159:	halt         
  1160:	load       0
  1165:	call       #9:_unbox@388
  1170:	load       1
  1175:	call       #9:_unbox@388
  1180:	load       12
  1185:	dcall        
  1186:	ret          

6. Run Bytecode:
Trace:
  0000:	br         88		stack=[ ], calls=[ _main ]
  0088:	br         201		stack=[ ], calls=[ _main ]
  0201:	br         212		stack=[ ], calls=[ _main ]
  0212:	br         223		stack=[ ], calls=[ _main ]
  0223:	br         234		stack=[ ], calls=[ _main ]
  0234:	br         245		stack=[ ], calls=[ _main ]
  0245:	struct     1		stack=[ ], calls=[ _main ]
  0250:	call       #1:A_new()@6		stack=[ [null] ], calls=[ _main ]
  0006:	struct     3		stack=[ ], calls=[ _main A_new() ]
  0011:	store      1		stack=[ [null, null, null] ], calls=[ _main A_new() ]
  0016:	iconst     101		stack=[ ], calls=[ _main A_new() ]
  0021:	load       1		stack=[ 101 ], calls=[ _main A_new() ]
  0026:	fstore     0		stack=[ 101 [null, null, null] ], calls=[ _main A_new() ]
  0031:	iconst     100		stack=[ ], calls=[ _main A_new() ]
  0036:	load       1		stack=[ 100 ], calls=[ _main A_new() ]
  0041:	fstore     1		stack=[ 100 [101, null, null] ], calls=[ _main A_new() ]
  0046:	null         		stack=[ ], calls=[ _main A_new() ]
  0047:	load       1		stack=[ 0 ], calls=[ _main A_new() ]
  0052:	fstore     2		stack=[ 0 [101, 100, null] ], calls=[ _main A_new() ]
  0057:	load       1		stack=[ ], calls=[ _main A_new() ]
  0062:	load       0		stack=[ [101, 100, 0] ], calls=[ _main A_new() ]
  0067:	fstore     0		stack=[ [101, 100, 0] [null] ], calls=[ _main A_new() ]
  0072:	load       0		stack=[ ], calls=[ _main A_new() ]
  0077:	call       #0:A_init()@5		stack=[ [[101, 100, 0]] ], calls=[ _main A_new() ]
  0005:	ret          		stack=[ ], calls=[ _main A_new() A_init() ]
  0082:	load       0		stack=[ ], calls=[ _main A_new() ]
  0087:	ret          		stack=[ [[101, 100, 0]] ], calls=[ _main A_new() ]
  0255:	store      0		stack=[ [[101, 100, 0]] ], calls=[ _main ]
  0260:	load       0		stack=[ ], calls=[ _main ]
  0265:	load       0		stack=[ [[101, 100, 0]] ], calls=[ _main ]
  0270:	call       #4:foo(A,A)@206		stack=[ [[101, 100, 0]] [[101, 100, 0]] ], calls=[ _main ]
  0206:	iconst     1		stack=[ ], calls=[ _main foo(A,A) ]
  0211:	ret          		stack=[ 1 ], calls=[ _main foo(A,A) ]
1
 */
