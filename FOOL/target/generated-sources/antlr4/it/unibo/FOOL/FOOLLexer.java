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
		SEMIC=1, COLON=2, COMMA=3, EQ=4, ASM=5, PLUS=6, TIMES=7, TRUE=8, FALSE=9, 
		LPAR=10, RPAR=11, CLPAR=12, CRPAR=13, IF=14, THEN=15, ELSE=16, PRINT=17, 
		LET=18, IN=19, VAR=20, FUN=21, INT=22, BOOL=23, INTEGER=24, ID=25, WS=26, 
		LINECOMENTS=27, BLOCKCOMENTS=28, ERR=29;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	public static final String[] ruleNames = {
		"SEMIC", "COLON", "COMMA", "EQ", "ASM", "PLUS", "TIMES", "TRUE", "FALSE", 
		"LPAR", "RPAR", "CLPAR", "CRPAR", "IF", "THEN", "ELSE", "PRINT", "LET", 
		"IN", "VAR", "FUN", "INT", "BOOL", "DIGIT", "INTEGER", "CHAR", "ID", "WS", 
		"LINECOMENTS", "BLOCKCOMENTS", "ERR"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "';'", "':'", "','", "'=='", "'='", "'+'", "'*'", "'true'", "'false'", 
		"'('", "')'", "'{'", "'}'", "'if'", "'then'", "'else'", "'print'", "'let'", 
		"'in'", "'var'", "'fun'", "'int'", "'bool'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, "SEMIC", "COLON", "COMMA", "EQ", "ASM", "PLUS", "TIMES", "TRUE", 
		"FALSE", "LPAR", "RPAR", "CLPAR", "CRPAR", "IF", "THEN", "ELSE", "PRINT", 
		"LET", "IN", "VAR", "FUN", "INT", "BOOL", "INTEGER", "ID", "WS", "LINECOMENTS", 
		"BLOCKCOMENTS", "ERR"
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
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\37\u00cb\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31"+
		"\t\31\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t"+
		" \3\2\3\2\3\3\3\3\3\4\3\4\3\5\3\5\3\5\3\6\3\6\3\7\3\7\3\b\3\b\3\t\3\t"+
		"\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\n\3\n\3\13\3\13\3\f\3\f\3\r\3\r\3\16\3"+
		"\16\3\17\3\17\3\17\3\20\3\20\3\20\3\20\3\20\3\21\3\21\3\21\3\21\3\21\3"+
		"\22\3\22\3\22\3\22\3\22\3\22\3\23\3\23\3\23\3\23\3\24\3\24\3\24\3\25\3"+
		"\25\3\25\3\25\3\26\3\26\3\26\3\26\3\27\3\27\3\27\3\27\3\30\3\30\3\30\3"+
		"\30\3\30\3\31\3\31\3\32\5\32\u0092\n\32\3\32\6\32\u0095\n\32\r\32\16\32"+
		"\u0096\3\33\3\33\3\34\3\34\3\34\7\34\u009e\n\34\f\34\16\34\u00a1\13\34"+
		"\3\35\6\35\u00a4\n\35\r\35\16\35\u00a5\3\35\3\35\3\36\3\36\3\36\3\36\7"+
		"\36\u00ae\n\36\f\36\16\36\u00b1\13\36\3\36\6\36\u00b4\n\36\r\36\16\36"+
		"\u00b5\3\36\3\36\3\37\3\37\3\37\3\37\7\37\u00be\n\37\f\37\16\37\u00c1"+
		"\13\37\3\37\3\37\3\37\3\37\3\37\3 \3 \3 \3 \4\u00af\u00bf\2!\3\3\5\4\7"+
		"\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37\21!\22"+
		"#\23%\24\'\25)\26+\27-\30/\31\61\2\63\32\65\2\67\339\34;\35=\36?\37\3"+
		"\2\5\4\2C\\c|\5\2\13\f\17\17\"\"\4\2\f\f\17\17\2\u00d0\2\3\3\2\2\2\2\5"+
		"\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2"+
		"\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33"+
		"\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2"+
		"\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2\63\3\2\2\2\2"+
		"\67\3\2\2\2\29\3\2\2\2\2;\3\2\2\2\2=\3\2\2\2\2?\3\2\2\2\3A\3\2\2\2\5C"+
		"\3\2\2\2\7E\3\2\2\2\tG\3\2\2\2\13J\3\2\2\2\rL\3\2\2\2\17N\3\2\2\2\21P"+
		"\3\2\2\2\23U\3\2\2\2\25[\3\2\2\2\27]\3\2\2\2\31_\3\2\2\2\33a\3\2\2\2\35"+
		"c\3\2\2\2\37f\3\2\2\2!k\3\2\2\2#p\3\2\2\2%v\3\2\2\2\'z\3\2\2\2)}\3\2\2"+
		"\2+\u0081\3\2\2\2-\u0085\3\2\2\2/\u0089\3\2\2\2\61\u008e\3\2\2\2\63\u0091"+
		"\3\2\2\2\65\u0098\3\2\2\2\67\u009a\3\2\2\29\u00a3\3\2\2\2;\u00a9\3\2\2"+
		"\2=\u00b9\3\2\2\2?\u00c7\3\2\2\2AB\7=\2\2B\4\3\2\2\2CD\7<\2\2D\6\3\2\2"+
		"\2EF\7.\2\2F\b\3\2\2\2GH\7?\2\2HI\7?\2\2I\n\3\2\2\2JK\7?\2\2K\f\3\2\2"+
		"\2LM\7-\2\2M\16\3\2\2\2NO\7,\2\2O\20\3\2\2\2PQ\7v\2\2QR\7t\2\2RS\7w\2"+
		"\2ST\7g\2\2T\22\3\2\2\2UV\7h\2\2VW\7c\2\2WX\7n\2\2XY\7u\2\2YZ\7g\2\2Z"+
		"\24\3\2\2\2[\\\7*\2\2\\\26\3\2\2\2]^\7+\2\2^\30\3\2\2\2_`\7}\2\2`\32\3"+
		"\2\2\2ab\7\177\2\2b\34\3\2\2\2cd\7k\2\2de\7h\2\2e\36\3\2\2\2fg\7v\2\2"+
		"gh\7j\2\2hi\7g\2\2ij\7p\2\2j \3\2\2\2kl\7g\2\2lm\7n\2\2mn\7u\2\2no\7g"+
		"\2\2o\"\3\2\2\2pq\7r\2\2qr\7t\2\2rs\7k\2\2st\7p\2\2tu\7v\2\2u$\3\2\2\2"+
		"vw\7n\2\2wx\7g\2\2xy\7v\2\2y&\3\2\2\2z{\7k\2\2{|\7p\2\2|(\3\2\2\2}~\7"+
		"x\2\2~\177\7c\2\2\177\u0080\7t\2\2\u0080*\3\2\2\2\u0081\u0082\7h\2\2\u0082"+
		"\u0083\7w\2\2\u0083\u0084\7p\2\2\u0084,\3\2\2\2\u0085\u0086\7k\2\2\u0086"+
		"\u0087\7p\2\2\u0087\u0088\7v\2\2\u0088.\3\2\2\2\u0089\u008a\7d\2\2\u008a"+
		"\u008b\7q\2\2\u008b\u008c\7q\2\2\u008c\u008d\7n\2\2\u008d\60\3\2\2\2\u008e"+
		"\u008f\4\62;\2\u008f\62\3\2\2\2\u0090\u0092\7/\2\2\u0091\u0090\3\2\2\2"+
		"\u0091\u0092\3\2\2\2\u0092\u0094\3\2\2\2\u0093\u0095\5\61\31\2\u0094\u0093"+
		"\3\2\2\2\u0095\u0096\3\2\2\2\u0096\u0094\3\2\2\2\u0096\u0097\3\2\2\2\u0097"+
		"\64\3\2\2\2\u0098\u0099\t\2\2\2\u0099\66\3\2\2\2\u009a\u009f\5\65\33\2"+
		"\u009b\u009e\5\65\33\2\u009c\u009e\5\61\31\2\u009d\u009b\3\2\2\2\u009d"+
		"\u009c\3\2\2\2\u009e\u00a1\3\2\2\2\u009f\u009d\3\2\2\2\u009f\u00a0\3\2"+
		"\2\2\u00a08\3\2\2\2\u00a1\u009f\3\2\2\2\u00a2\u00a4\t\3\2\2\u00a3\u00a2"+
		"\3\2\2\2\u00a4\u00a5\3\2\2\2\u00a5\u00a3\3\2\2\2\u00a5\u00a6\3\2\2\2\u00a6"+
		"\u00a7\3\2\2\2\u00a7\u00a8\b\35\2\2\u00a8:\3\2\2\2\u00a9\u00aa\7\61\2"+
		"\2\u00aa\u00ab\7\61\2\2\u00ab\u00af\3\2\2\2\u00ac\u00ae\13\2\2\2\u00ad"+
		"\u00ac\3\2\2\2\u00ae\u00b1\3\2\2\2\u00af\u00b0\3\2\2\2\u00af\u00ad\3\2"+
		"\2\2\u00b0\u00b3\3\2\2\2\u00b1\u00af\3\2\2\2\u00b2\u00b4\t\4\2\2\u00b3"+
		"\u00b2\3\2\2\2\u00b4\u00b5\3\2\2\2\u00b5\u00b3\3\2\2\2\u00b5\u00b6\3\2"+
		"\2\2\u00b6\u00b7\3\2\2\2\u00b7\u00b8\b\36\2\2\u00b8<\3\2\2\2\u00b9\u00ba"+
		"\7\61\2\2\u00ba\u00bb\7,\2\2\u00bb\u00bf\3\2\2\2\u00bc\u00be\13\2\2\2"+
		"\u00bd\u00bc\3\2\2\2\u00be\u00c1\3\2\2\2\u00bf\u00c0\3\2\2\2\u00bf\u00bd"+
		"\3\2\2\2\u00c0\u00c2\3\2\2\2\u00c1\u00bf\3\2\2\2\u00c2\u00c3\7,\2\2\u00c3"+
		"\u00c4\7\61\2\2\u00c4\u00c5\3\2\2\2\u00c5\u00c6\b\37\2\2\u00c6>\3\2\2"+
		"\2\u00c7\u00c8\13\2\2\2\u00c8\u00c9\3\2\2\2\u00c9\u00ca\b \3\2\u00ca@"+
		"\3\2\2\2\13\2\u0091\u0096\u009d\u009f\u00a5\u00af\u00b5\u00bf\4\b\2\2"+
		"\2\3\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}