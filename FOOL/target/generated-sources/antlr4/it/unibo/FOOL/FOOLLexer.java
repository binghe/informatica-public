// Generated from FOOL.g4 by ANTLR 4.7
package it.unibo.FOOL;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class FOOLLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.7", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, SEMIC=3, COLON=4, COMMA=5, EQ=6, ASM=7, PLUS=8, TIMES=9, 
		TRUE=10, FALSE=11, LPAR=12, RPAR=13, CLPAR=14, CRPAR=15, IF=16, THEN=17, 
		ELSE=18, PRINT=19, LET=20, IN=21, VAR=22, FUN=23, INT=24, BOOL=25, CLASS=26, 
		OBJECT=27, INHER=28, END=29, INTEGER=30, ID=31, WS=32, LINECOMENTS=33, 
		BLOCKCOMENTS=34, ERR=35;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	public static final String[] ruleNames = {
		"T__0", "T__1", "SEMIC", "COLON", "COMMA", "EQ", "ASM", "PLUS", "TIMES", 
		"TRUE", "FALSE", "LPAR", "RPAR", "CLPAR", "CRPAR", "IF", "THEN", "ELSE", 
		"PRINT", "LET", "IN", "VAR", "FUN", "INT", "BOOL", "CLASS", "OBJECT", 
		"INHER", "END", "DIGIT", "INTEGER", "CHAR", "ID", "WS", "LINECOMENTS", 
		"BLOCKCOMENTS", "ERR"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "'new'", "'.'", "';'", "':'", "','", "'=='", "'='", "'+'", "'*'", 
		"'true'", "'false'", "'('", "')'", "'{'", "'}'", "'if'", "'then'", "'else'", 
		"'print'", "'let'", "'in'", "'var'", "'fun'", "'int'", "'bool'", "'class'", 
		"'object'", "'inherit'", "'end'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, null, null, "SEMIC", "COLON", "COMMA", "EQ", "ASM", "PLUS", "TIMES", 
		"TRUE", "FALSE", "LPAR", "RPAR", "CLPAR", "CRPAR", "IF", "THEN", "ELSE", 
		"PRINT", "LET", "IN", "VAR", "FUN", "INT", "BOOL", "CLASS", "OBJECT", 
		"INHER", "END", "INTEGER", "ID", "WS", "LINECOMENTS", "BLOCKCOMENTS", 
		"ERR"
	};
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


	public FOOLLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "FOOL.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2%\u00f6\b\1\4\2\t"+
		"\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\3\2\3\2\3\2\3\2\3\3\3\3\3\4\3\4\3"+
		"\5\3\5\3\6\3\6\3\7\3\7\3\7\3\b\3\b\3\t\3\t\3\n\3\n\3\13\3\13\3\13\3\13"+
		"\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\r\3\r\3\16\3\16\3\17\3\17\3\20\3\20\3"+
		"\21\3\21\3\21\3\22\3\22\3\22\3\22\3\22\3\23\3\23\3\23\3\23\3\23\3\24\3"+
		"\24\3\24\3\24\3\24\3\24\3\25\3\25\3\25\3\25\3\26\3\26\3\26\3\27\3\27\3"+
		"\27\3\27\3\30\3\30\3\30\3\30\3\31\3\31\3\31\3\31\3\32\3\32\3\32\3\32\3"+
		"\32\3\33\3\33\3\33\3\33\3\33\3\33\3\34\3\34\3\34\3\34\3\34\3\34\3\34\3"+
		"\35\3\35\3\35\3\35\3\35\3\35\3\35\3\35\3\36\3\36\3\36\3\36\3\37\3\37\3"+
		" \5 \u00bd\n \3 \6 \u00c0\n \r \16 \u00c1\3!\3!\3\"\3\"\3\"\7\"\u00c9"+
		"\n\"\f\"\16\"\u00cc\13\"\3#\6#\u00cf\n#\r#\16#\u00d0\3#\3#\3$\3$\3$\3"+
		"$\7$\u00d9\n$\f$\16$\u00dc\13$\3$\6$\u00df\n$\r$\16$\u00e0\3$\3$\3%\3"+
		"%\3%\3%\7%\u00e9\n%\f%\16%\u00ec\13%\3%\3%\3%\3%\3%\3&\3&\3&\3&\4\u00da"+
		"\u00ea\2\'\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33"+
		"\17\35\20\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\65\34\67"+
		"\359\36;\37=\2? A\2C!E\"G#I$K%\3\2\5\4\2C\\c|\5\2\13\f\17\17\"\"\4\2\f"+
		"\f\17\17\2\u00fb\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13"+
		"\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2"+
		"\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2"+
		"!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3"+
		"\2\2\2\2/\3\2\2\2\2\61\3\2\2\2\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3\2\2\2"+
		"\29\3\2\2\2\2;\3\2\2\2\2?\3\2\2\2\2C\3\2\2\2\2E\3\2\2\2\2G\3\2\2\2\2I"+
		"\3\2\2\2\2K\3\2\2\2\3M\3\2\2\2\5Q\3\2\2\2\7S\3\2\2\2\tU\3\2\2\2\13W\3"+
		"\2\2\2\rY\3\2\2\2\17\\\3\2\2\2\21^\3\2\2\2\23`\3\2\2\2\25b\3\2\2\2\27"+
		"g\3\2\2\2\31m\3\2\2\2\33o\3\2\2\2\35q\3\2\2\2\37s\3\2\2\2!u\3\2\2\2#x"+
		"\3\2\2\2%}\3\2\2\2\'\u0082\3\2\2\2)\u0088\3\2\2\2+\u008c\3\2\2\2-\u008f"+
		"\3\2\2\2/\u0093\3\2\2\2\61\u0097\3\2\2\2\63\u009b\3\2\2\2\65\u00a0\3\2"+
		"\2\2\67\u00a6\3\2\2\29\u00ad\3\2\2\2;\u00b5\3\2\2\2=\u00b9\3\2\2\2?\u00bc"+
		"\3\2\2\2A\u00c3\3\2\2\2C\u00c5\3\2\2\2E\u00ce\3\2\2\2G\u00d4\3\2\2\2I"+
		"\u00e4\3\2\2\2K\u00f2\3\2\2\2MN\7p\2\2NO\7g\2\2OP\7y\2\2P\4\3\2\2\2QR"+
		"\7\60\2\2R\6\3\2\2\2ST\7=\2\2T\b\3\2\2\2UV\7<\2\2V\n\3\2\2\2WX\7.\2\2"+
		"X\f\3\2\2\2YZ\7?\2\2Z[\7?\2\2[\16\3\2\2\2\\]\7?\2\2]\20\3\2\2\2^_\7-\2"+
		"\2_\22\3\2\2\2`a\7,\2\2a\24\3\2\2\2bc\7v\2\2cd\7t\2\2de\7w\2\2ef\7g\2"+
		"\2f\26\3\2\2\2gh\7h\2\2hi\7c\2\2ij\7n\2\2jk\7u\2\2kl\7g\2\2l\30\3\2\2"+
		"\2mn\7*\2\2n\32\3\2\2\2op\7+\2\2p\34\3\2\2\2qr\7}\2\2r\36\3\2\2\2st\7"+
		"\177\2\2t \3\2\2\2uv\7k\2\2vw\7h\2\2w\"\3\2\2\2xy\7v\2\2yz\7j\2\2z{\7"+
		"g\2\2{|\7p\2\2|$\3\2\2\2}~\7g\2\2~\177\7n\2\2\177\u0080\7u\2\2\u0080\u0081"+
		"\7g\2\2\u0081&\3\2\2\2\u0082\u0083\7r\2\2\u0083\u0084\7t\2\2\u0084\u0085"+
		"\7k\2\2\u0085\u0086\7p\2\2\u0086\u0087\7v\2\2\u0087(\3\2\2\2\u0088\u0089"+
		"\7n\2\2\u0089\u008a\7g\2\2\u008a\u008b\7v\2\2\u008b*\3\2\2\2\u008c\u008d"+
		"\7k\2\2\u008d\u008e\7p\2\2\u008e,\3\2\2\2\u008f\u0090\7x\2\2\u0090\u0091"+
		"\7c\2\2\u0091\u0092\7t\2\2\u0092.\3\2\2\2\u0093\u0094\7h\2\2\u0094\u0095"+
		"\7w\2\2\u0095\u0096\7p\2\2\u0096\60\3\2\2\2\u0097\u0098\7k\2\2\u0098\u0099"+
		"\7p\2\2\u0099\u009a\7v\2\2\u009a\62\3\2\2\2\u009b\u009c\7d\2\2\u009c\u009d"+
		"\7q\2\2\u009d\u009e\7q\2\2\u009e\u009f\7n\2\2\u009f\64\3\2\2\2\u00a0\u00a1"+
		"\7e\2\2\u00a1\u00a2\7n\2\2\u00a2\u00a3\7c\2\2\u00a3\u00a4\7u\2\2\u00a4"+
		"\u00a5\7u\2\2\u00a5\66\3\2\2\2\u00a6\u00a7\7q\2\2\u00a7\u00a8\7d\2\2\u00a8"+
		"\u00a9\7l\2\2\u00a9\u00aa\7g\2\2\u00aa\u00ab\7e\2\2\u00ab\u00ac\7v\2\2"+
		"\u00ac8\3\2\2\2\u00ad\u00ae\7k\2\2\u00ae\u00af\7p\2\2\u00af\u00b0\7j\2"+
		"\2\u00b0\u00b1\7g\2\2\u00b1\u00b2\7t\2\2\u00b2\u00b3\7k\2\2\u00b3\u00b4"+
		"\7v\2\2\u00b4:\3\2\2\2\u00b5\u00b6\7g\2\2\u00b6\u00b7\7p\2\2\u00b7\u00b8"+
		"\7f\2\2\u00b8<\3\2\2\2\u00b9\u00ba\4\62;\2\u00ba>\3\2\2\2\u00bb\u00bd"+
		"\7/\2\2\u00bc\u00bb\3\2\2\2\u00bc\u00bd\3\2\2\2\u00bd\u00bf\3\2\2\2\u00be"+
		"\u00c0\5=\37\2\u00bf\u00be\3\2\2\2\u00c0\u00c1\3\2\2\2\u00c1\u00bf\3\2"+
		"\2\2\u00c1\u00c2\3\2\2\2\u00c2@\3\2\2\2\u00c3\u00c4\t\2\2\2\u00c4B\3\2"+
		"\2\2\u00c5\u00ca\5A!\2\u00c6\u00c9\5A!\2\u00c7\u00c9\5=\37\2\u00c8\u00c6"+
		"\3\2\2\2\u00c8\u00c7\3\2\2\2\u00c9\u00cc\3\2\2\2\u00ca\u00c8\3\2\2\2\u00ca"+
		"\u00cb\3\2\2\2\u00cbD\3\2\2\2\u00cc\u00ca\3\2\2\2\u00cd\u00cf\t\3\2\2"+
		"\u00ce\u00cd\3\2\2\2\u00cf\u00d0\3\2\2\2\u00d0\u00ce\3\2\2\2\u00d0\u00d1"+
		"\3\2\2\2\u00d1\u00d2\3\2\2\2\u00d2\u00d3\b#\2\2\u00d3F\3\2\2\2\u00d4\u00d5"+
		"\7\61\2\2\u00d5\u00d6\7\61\2\2\u00d6\u00da\3\2\2\2\u00d7\u00d9\13\2\2"+
		"\2\u00d8\u00d7\3\2\2\2\u00d9\u00dc\3\2\2\2\u00da\u00db\3\2\2\2\u00da\u00d8"+
		"\3\2\2\2\u00db\u00de\3\2\2\2\u00dc\u00da\3\2\2\2\u00dd\u00df\t\4\2\2\u00de"+
		"\u00dd\3\2\2\2\u00df\u00e0\3\2\2\2\u00e0\u00de\3\2\2\2\u00e0\u00e1\3\2"+
		"\2\2\u00e1\u00e2\3\2\2\2\u00e2\u00e3\b$\2\2\u00e3H\3\2\2\2\u00e4\u00e5"+
		"\7\61\2\2\u00e5\u00e6\7,\2\2\u00e6\u00ea\3\2\2\2\u00e7\u00e9\13\2\2\2"+
		"\u00e8\u00e7\3\2\2\2\u00e9\u00ec\3\2\2\2\u00ea\u00eb\3\2\2\2\u00ea\u00e8"+
		"\3\2\2\2\u00eb\u00ed\3\2\2\2\u00ec\u00ea\3\2\2\2\u00ed\u00ee\7,\2\2\u00ee"+
		"\u00ef\7\61\2\2\u00ef\u00f0\3\2\2\2\u00f0\u00f1\b%\2\2\u00f1J\3\2\2\2"+
		"\u00f2\u00f3\13\2\2\2\u00f3\u00f4\3\2\2\2\u00f4\u00f5\b&\3\2\u00f5L\3"+
		"\2\2\2\13\2\u00bc\u00c1\u00c8\u00ca\u00d0\u00da\u00e0\u00ea\4\b\2\2\2"+
		"\3\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}