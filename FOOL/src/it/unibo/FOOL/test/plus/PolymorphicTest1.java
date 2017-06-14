/**
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.plus;

/*
 * Polymorphic Type Test #1: classic multimethods
 */

import static org.junit.Assert.assertEquals;
import org.junit.Test;
import it.unibo.FOOL.test.*;

public final class PolymorphicTest1 extends UnitTest {
    @Test
    public void testPolymorphicType() {
	prog = "   class A = object end;				\n"
		+ "class B = object inherit A; end;			\n"
		+ "let int foo(A o1, A o2) 1;				\n"
		+ "    int foo(A o1, B o2) 2;				\n"
		+ "    int foo(B o1, A o2) 3;				\n"
		+ "    int foo(B o1, B o2) 4;				\n"
		+ "    A obj = new B();					\n"
		+ "in obj.foo(obj) + 6;					\n";
	result = 10;
	trace = true;
	assertEquals(run(), result);
    }
}

/** @formatter:off
6. Run Bytecode:
Trace:
  0000:	br         88		stack=[ ], calls=[ _main ]
  0088:	br         201		stack=[ ], calls=[ _main ]
  0201:	br         212		stack=[ ], calls=[ _main ]
  0212:	br         223		stack=[ ], calls=[ _main ]
  0223:	br         234		stack=[ ], calls=[ _main ]
  0234:	br         245		stack=[ ], calls=[ _main ]
  0245:	struct     1		stack=[ ], calls=[ _main ]
  0250:	call       #3:B_new()@104		stack=[ [null] ], calls=[ _main ]
  0104:	struct     4		stack=[ ], calls=[ _main B_new() ]
  0109:	store      1		stack=[ [null, null, null, null] ], calls=[ _main B_new() ]
  0114:	iconst     102		stack=[ ], calls=[ _main B_new() ]
  0119:	load       1		stack=[ 102 ], calls=[ _main B_new() ]
  0124:	fstore     0		stack=[ 102 [null, null, null, null] ], calls=[ _main B_new() ]
  0129:	iconst     101		stack=[ ], calls=[ _main B_new() ]
  0134:	load       1		stack=[ 101 ], calls=[ _main B_new() ]
  0139:	fstore     1		stack=[ 101 [102, null, null, null] ], calls=[ _main B_new() ]
  0144:	iconst     100		stack=[ ], calls=[ _main B_new() ]
  0149:	load       1		stack=[ 100 ], calls=[ _main B_new() ]
  0154:	fstore     2		stack=[ 100 [102, 101, null, null] ], calls=[ _main B_new() ]
  0159:	null         		stack=[ ], calls=[ _main B_new() ]
  0160:	load       1		stack=[ 0 ], calls=[ _main B_new() ]
  0165:	fstore     3		stack=[ 0 [102, 101, 100, null] ], calls=[ _main B_new() ]
  0170:	load       1		stack=[ ], calls=[ _main B_new() ]
  0175:	load       0		stack=[ [102, 101, 100, 0] ], calls=[ _main B_new() ]
  0180:	fstore     0		stack=[ [102, 101, 100, 0] [null] ], calls=[ _main B_new() ]
  0185:	load       0		stack=[ ], calls=[ _main B_new() ]
  0190:	call       #2:B_init()@93		stack=[ [[102, 101, 100, 0]] ], calls=[ _main B_new() ]
  0093:	load       0		stack=[ ], calls=[ _main B_new() B_init() ]
  0098:	call       #0:A_init()@5		stack=[ [[102, 101, 100, 0]] ], calls=[ _main B_new() B_init() ]
  0005:	ret          		stack=[ ], calls=[ _main B_new() B_init() A_init() ]
  0103:	ret          		stack=[ ], calls=[ _main B_new() B_init() ]
  0195:	load       0		stack=[ ], calls=[ _main B_new() ]
  0200:	ret          		stack=[ [[102, 101, 100, 0]] ], calls=[ _main B_new() ]
  0255:	store      0		stack=[ [[102, 101, 100, 0]] ], calls=[ _main ]
  0260:	load       0		stack=[ ], calls=[ _main ]
  0265:	load       0		stack=[ [[102, 101, 100, 0]] ], calls=[ _main ]
  0270:	call       #8:foo@519		stack=[ [[102, 101, 100, 0]] [[102, 101, 100, 0]] ], calls=[ _main ]
  0519:	load       0		stack=[ ], calls=[ _main foo ]
  0524:	fload      0		stack=[ [[102, 101, 100, 0]] ], calls=[ _main foo ]
  0529:	store      2		stack=[ [102, 101, 100, 0] ], calls=[ _main foo ]
  0534:	load       1		stack=[ ], calls=[ _main foo ]
  0539:	fload      0		stack=[ [[102, 101, 100, 0]] ], calls=[ _main foo ]
  0544:	store      3		stack=[ [102, 101, 100, 0] ], calls=[ _main foo ]
  0549:	struct     4		stack=[ ], calls=[ _main foo ]
  0554:	store      4		stack=[ [null, null, null, null] ], calls=[ _main foo ]
  0559:	iconst     102		stack=[ ], calls=[ _main foo ]
  0564:	load       4		stack=[ 102 ], calls=[ _main foo ]
  0569:	fstore     0		stack=[ 102 [null, null, null, null] ], calls=[ _main foo ]
  0574:	iconst     101		stack=[ ], calls=[ _main foo ]
  0579:	load       4		stack=[ 101 ], calls=[ _main foo ]
  0584:	fstore     1		stack=[ 101 [102, null, null, null] ], calls=[ _main foo ]
  0589:	iconst     100		stack=[ ], calls=[ _main foo ]
  0594:	load       4		stack=[ 100 ], calls=[ _main foo ]
  0599:	fstore     2		stack=[ 100 [102, 101, null, null] ], calls=[ _main foo ]
  0604:	null         		stack=[ ], calls=[ _main foo ]
  0605:	load       4		stack=[ 0 ], calls=[ _main foo ]
  0610:	fstore     3		stack=[ 0 [102, 101, 100, null] ], calls=[ _main foo ]
  0615:	load       2		stack=[ ], calls=[ _main foo ]
  0620:	load       4		stack=[ [102, 101, 100, 0] ], calls=[ _main foo ]
  0625:	call       #9:_subclassp@282		stack=[ [102, 101, 100, 0] [102, 101, 100, 0] ], calls=[ _main foo ]
  0282:	iconst     0		stack=[ ], calls=[ _main foo _subclassp ]
  0287:	store      2		stack=[ 0 ], calls=[ _main foo _subclassp ]
  0292:	iconst     0		stack=[ ], calls=[ _main foo _subclassp ]
  0297:	store      3		stack=[ 0 ], calls=[ _main foo _subclassp ]
  0302:	load       1		stack=[ ], calls=[ _main foo _subclassp ]
  0307:	fload      0		stack=[ [102, 101, 100, 0] ], calls=[ _main foo _subclassp ]
  0312:	store      4		stack=[ 102 ], calls=[ _main foo _subclassp ]
  0317:	load       0		stack=[ ], calls=[ _main foo _subclassp ]
  0322:	load       2		stack=[ [102, 101, 100, 0] ], calls=[ _main foo _subclassp ]
  0327:	dfload       		stack=[ [102, 101, 100, 0] 0 ], calls=[ _main foo _subclassp ]
  0328:	load       3		stack=[ 102 ], calls=[ _main foo _subclassp ]
  0333:	ieq          		stack=[ 102 0 ], calls=[ _main foo _subclassp ]
  0334:	brt        392		stack=[ 0 ], calls=[ _main foo _subclassp ]
  0339:	load       0		stack=[ ], calls=[ _main foo _subclassp ]
  0344:	load       2		stack=[ [102, 101, 100, 0] ], calls=[ _main foo _subclassp ]
  0349:	dfload       		stack=[ [102, 101, 100, 0] 0 ], calls=[ _main foo _subclassp ]
  0350:	load       4		stack=[ 102 ], calls=[ _main foo _subclassp ]
  0355:	ieq          		stack=[ 102 102 ], calls=[ _main foo _subclassp ]
  0356:	brt        382		stack=[ 1 ], calls=[ _main foo _subclassp ]
  0382:	iconst     1		stack=[ ], calls=[ _main foo _subclassp ]
  0387:	br         393		stack=[ 1 ], calls=[ _main foo _subclassp ]
  0393:	ret          		stack=[ 1 ], calls=[ _main foo _subclassp ]
  0630:	brf        736		stack=[ 1 ], calls=[ _main foo ]
  0635:	struct     4		stack=[ ], calls=[ _main foo ]
  0640:	store      5		stack=[ [null, null, null, null] ], calls=[ _main foo ]
  0645:	iconst     102		stack=[ ], calls=[ _main foo ]
  0650:	load       5		stack=[ 102 ], calls=[ _main foo ]
  0655:	fstore     0		stack=[ 102 [null, null, null, null] ], calls=[ _main foo ]
  0660:	iconst     101		stack=[ ], calls=[ _main foo ]
  0665:	load       5		stack=[ 101 ], calls=[ _main foo ]
  0670:	fstore     1		stack=[ 101 [102, null, null, null] ], calls=[ _main foo ]
  0675:	iconst     100		stack=[ ], calls=[ _main foo ]
  0680:	load       5		stack=[ 100 ], calls=[ _main foo ]
  0685:	fstore     2		stack=[ 100 [102, 101, null, null] ], calls=[ _main foo ]
  0690:	null         		stack=[ ], calls=[ _main foo ]
  0691:	load       5		stack=[ 0 ], calls=[ _main foo ]
  0696:	fstore     3		stack=[ 0 [102, 101, 100, null] ], calls=[ _main foo ]
  0701:	load       2		stack=[ ], calls=[ _main foo ]
  0706:	load       5		stack=[ [102, 101, 100, 0] ], calls=[ _main foo ]
  0711:	call       #9:_subclassp@282		stack=[ [102, 101, 100, 0] [102, 101, 100, 0] ], calls=[ _main foo ]
  0282:	iconst     0		stack=[ ], calls=[ _main foo _subclassp ]
  0287:	store      2		stack=[ 0 ], calls=[ _main foo _subclassp ]
  0292:	iconst     0		stack=[ ], calls=[ _main foo _subclassp ]
  0297:	store      3		stack=[ 0 ], calls=[ _main foo _subclassp ]
  0302:	load       1		stack=[ ], calls=[ _main foo _subclassp ]
  0307:	fload      0		stack=[ [102, 101, 100, 0] ], calls=[ _main foo _subclassp ]
  0312:	store      4		stack=[ 102 ], calls=[ _main foo _subclassp ]
  0317:	load       0		stack=[ ], calls=[ _main foo _subclassp ]
  0322:	load       2		stack=[ [102, 101, 100, 0] ], calls=[ _main foo _subclassp ]
  0327:	dfload       		stack=[ [102, 101, 100, 0] 0 ], calls=[ _main foo _subclassp ]
  0328:	load       3		stack=[ 102 ], calls=[ _main foo _subclassp ]
  0333:	ieq          		stack=[ 102 0 ], calls=[ _main foo _subclassp ]
  0334:	brt        392		stack=[ 0 ], calls=[ _main foo _subclassp ]
  0339:	load       0		stack=[ ], calls=[ _main foo _subclassp ]
  0344:	load       2		stack=[ [102, 101, 100, 0] ], calls=[ _main foo _subclassp ]
  0349:	dfload       		stack=[ [102, 101, 100, 0] 0 ], calls=[ _main foo _subclassp ]
  0350:	load       4		stack=[ 102 ], calls=[ _main foo _subclassp ]
  0355:	ieq          		stack=[ 102 102 ], calls=[ _main foo _subclassp ]
  0356:	brt        382		stack=[ 1 ], calls=[ _main foo _subclassp ]
  0382:	iconst     1		stack=[ ], calls=[ _main foo _subclassp ]
  0387:	br         393		stack=[ 1 ], calls=[ _main foo _subclassp ]
  0393:	ret          		stack=[ 1 ], calls=[ _main foo _subclassp ]
  0716:	brf        736		stack=[ 1 ], calls=[ _main foo ]
  0721:	pconst     #7:foo(B,B)@239		stack=[ ], calls=[ _main foo ]
  0726:	store      12		stack=[ 7 ], calls=[ _main foo ]
  0731:	br         1249		stack=[ ], calls=[ _main foo ]
  1249:	load       0		stack=[ ], calls=[ _main foo ]
  1254:	call       #11:_unbox@476		stack=[ [[102, 101, 100, 0]] ], calls=[ _main foo ]
  0476:	load       0		stack=[ ], calls=[ _main foo _unbox ]
  0481:	fload      0		stack=[ [[102, 101, 100, 0]] ], calls=[ _main foo _unbox ]
  0486:	fload      1		stack=[ [102, 101, 100, 0] ], calls=[ _main foo _unbox ]
  0491:	null         		stack=[ 101 ], calls=[ _main foo _unbox ]
  0492:	ieq          		stack=[ 101 0 ], calls=[ _main foo _unbox ]
  0493:	brt        508		stack=[ 0 ], calls=[ _main foo _unbox ]
  0498:	load       0		stack=[ ], calls=[ _main foo _unbox ]
  0503:	br         518		stack=[ [[102, 101, 100, 0]] ], calls=[ _main foo _unbox ]
  0518:	ret          		stack=[ [[102, 101, 100, 0]] ], calls=[ _main foo _unbox ]
  1259:	load       1		stack=[ [[102, 101, 100, 0]] ], calls=[ _main foo ]
  1264:	call       #11:_unbox@476		stack=[ [[102, 101, 100, 0]] [[102, 101, 100, 0]] ], calls=[ _main foo ]
  0476:	load       0		stack=[ [[102, 101, 100, 0]] ], calls=[ _main foo _unbox ]
  0481:	fload      0		stack=[ [[102, 101, 100, 0]] [[102, 101, 100, 0]] ], calls=[ _main foo _unbox ]
  0486:	fload      1		stack=[ [[102, 101, 100, 0]] [102, 101, 100, 0] ], calls=[ _main foo _unbox ]
  0491:	null         		stack=[ [[102, 101, 100, 0]] 101 ], calls=[ _main foo _unbox ]
  0492:	ieq          		stack=[ [[102, 101, 100, 0]] 101 0 ], calls=[ _main foo _unbox ]
  0493:	brt        508		stack=[ [[102, 101, 100, 0]] 0 ], calls=[ _main foo _unbox ]
  0498:	load       0		stack=[ [[102, 101, 100, 0]] ], calls=[ _main foo _unbox ]
  0503:	br         518		stack=[ [[102, 101, 100, 0]] [[102, 101, 100, 0]] ], calls=[ _main foo _unbox ]
  0518:	ret          		stack=[ [[102, 101, 100, 0]] [[102, 101, 100, 0]] ], calls=[ _main foo _unbox ]
  1269:	load       12		stack=[ [[102, 101, 100, 0]] [[102, 101, 100, 0]] ], calls=[ _main foo ]
  1274:	dcall        		stack=[ [[102, 101, 100, 0]] [[102, 101, 100, 0]] 7 ], calls=[ _main foo ]
  0239:	iconst     4		stack=[ ], calls=[ _main foo foo(B,B) ]
  0244:	ret          		stack=[ 4 ], calls=[ _main foo foo(B,B) ]
  1275:	ret          		stack=[ 4 ], calls=[ _main foo ]
  0275:	iconst     6		stack=[ 4 ], calls=[ _main ]
  0280:	iadd         		stack=[ 4 6 ], calls=[ _main ]
10
*/
