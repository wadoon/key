package recoder.parser;

import java.io.IOException;
import java.io.PrintStream;

public class JavaCCParserTokenManager implements JavaCCParserConstants {
    public static final String[] jjstrLiteralImages = new String[]{
            "", null, null, null, null, null, null, null, null, null,
            null, null, null, "abstract", "assert", "@", "boolean", "break", "byte", "case",
            "catch", "char", "class", "const", "continue", "default", "do", "double", "else", "enum",
            "extends", "false", "final", "finally", "float", "for", "goto", "if", "implements", "import",
            "instanceof", "int", "interface", "long", "native", "new", "null", "package", "private", "protected",
            "public", "return", "short", "static", "super", "switch", "synchronized", "this", "throw", "throws",
            "transient", "true", "try", "void", "volatile", "while", "...", "strictfp", null, null,
            null, null, null, null, null, null, null, null, null, "(",
            ")", "{", "}", "[", "]", ";", ",", ".", "=", "<",
            "!", "~", "?", ":", "==", "<=", ">=", "!=", "||", "&&",
            "++", "--", "+", "-", "*", "/", "&", "|", "^", "%",
            "<<", "+=", "-=", "*=", "/=", "&=", "|=", "^=", "%=", "<<=",
            ">>=", ">>>=", ">>>", ">>", ">"};
    public static final String[] lexStateNames = new String[]{"DEFAULT", "IN_SINGLE_LINE_COMMENT", "IN_FORMAL_COMMENT", "IN_MULTI_LINE_COMMENT"};
    public static final int[] jjnewLexState = new int[]{
            -1, -1, -1, -1, -1, -1, 1, 2, 3, 0,
            0, 0, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1};
    static final long[] jjbitVec0 = new long[]{-2L, -1L, -1L, -1L};
    static final long[] jjbitVec2 = new long[]{0L, 0L, -1L, -1L};
    static final long[] jjbitVec3 = new long[]{-4503599625273342L, -8193L, -17525614051329L, 1297036692691091455L};
    static final long[] jjbitVec4 = new long[]{0L, 0L, 297242231151001600L, -36028797027352577L};
    static final long[] jjbitVec5 = new long[]{4503586742468607L, -65536L, -432556670460100609L, 70501888360451L};
    static final long[] jjbitVec6 = new long[]{0L, 288230376151711744L, -17179879616L, 4503599577006079L};
    static final long[] jjbitVec7 = new long[]{-1L, -1L, -4093L, 234187180623206815L};
    static final long[] jjbitVec8 = new long[]{-562949953421312L, -8547991553L, 255L, 1979120929931264L};
    static final long[] jjbitVec9 = new long[]{576460743713488896L, -562949953419265L, -1L, 2017613045381988351L};
    static final long[] jjbitVec10 = new long[]{35184371892224L, 0L, 274877906943L, 0L};
    static final long[] jjbitVec11 = new long[]{2594073385365405664L, 17163157504L, 271902628478820320L, 4222140488351744L};
    static final long[] jjbitVec12 = new long[]{247132830528276448L, 7881300924956672L, 2589004636761075680L, 4295032832L};
    static final long[] jjbitVec13 = new long[]{2579997437506199520L, 15837691904L, 270153412153034720L, 0L};
    static final long[] jjbitVec14 = new long[]{283724577500946400L, 12884901888L, 283724577500946400L, 13958643712L};
    static final long[] jjbitVec15 = new long[]{288228177128316896L, 12884901888L, 3457638613854978016L, 127L};
    static final long[] jjbitVec16 = new long[]{-9219431387180826626L, 127L, 2309762420256548246L, 805306463L};
    static final long[] jjbitVec17 = new long[]{1L, 8796093021951L, 3840L, 0L};
    static final long[] jjbitVec18 = new long[]{7679401525247L, 4128768L, -4294967296L, 36028797018898495L};
    static final long[] jjbitVec19 = new long[]{-1L, -2080374785L, -1065151889409L, 288230376151711743L};
    static final long[] jjbitVec20 = new long[]{-129L, -3263218305L, 9168625153884503423L, -140737496776899L};
    static final long[] jjbitVec21 = new long[]{-2160230401L, 134217599L, -4294967296L, 9007199254740991L};
    static final long[] jjbitVec22 = new long[]{-1L, 35923243902697471L, -4160749570L, 8796093022207L};
    static final long[] jjbitVec23 = new long[]{0L, 0L, 4503599627370495L, 134217728L};
    static final long[] jjbitVec24 = new long[]{-4294967296L, 72057594037927935L, 2199023255551L, 0L};
    static final long[] jjbitVec25 = new long[]{-1L, -1L, -4026531841L, 288230376151711743L};
    static final long[] jjbitVec26 = new long[]{-3233808385L, 4611686017001275199L, 6908521828386340863L, 2295745090394464220L};
    static final long[] jjbitVec27 = new long[]{Long.MIN_VALUE, -9223372036854775807L, 281470681743360L, 0L};
    static final long[] jjbitVec28 = new long[]{287031153606524036L, -4294967296L, 15L, 0L};
    static final long[] jjbitVec29 = new long[]{521858996278132960L, -2L, -6977224705L, Long.MAX_VALUE};
    static final long[] jjbitVec30 = new long[]{-527765581332512L, -1L, 72057589742993407L, 0L};
    static final long[] jjbitVec31 = new long[]{-1L, -1L, 18014398509481983L, 0L};
    static final long[] jjbitVec32 = new long[]{-1L, -1L, 274877906943L, 0L};
    static final long[] jjbitVec33 = new long[]{-1L, -1L, 8191L, 0L};
    static final long[] jjbitVec34 = new long[]{-1L, -1L, 68719476735L, 0L};
    static final long[] jjbitVec35 = new long[]{70368744177663L, 0L, 0L, 0L};
    static final long[] jjbitVec36 = new long[]{6881498030004502655L, -37L, 1125899906842623L, -524288L};
    static final long[] jjbitVec37 = new long[]{4611686018427387903L, -65536L, -196609L, 1152640029630136575L};
    static final long[] jjbitVec38 = new long[]{6755399441055744L, -11538275021824000L, -1L, 2305843009213693951L};
    static final long[] jjbitVec39 = new long[]{-8646911293141286896L, -137304735746L, Long.MAX_VALUE, 425688104188L};
    static final long[] jjbitVec40 = new long[]{0L, 0L, 297242235445968895L, -36028797027352577L};
    static final long[] jjbitVec41 = new long[]{-1L, 288230406216515583L, -17179879616L, 4503599577006079L};
    static final long[] jjbitVec42 = new long[]{-1L, -1L, -3973L, 234187180623206815L};
    static final long[] jjbitVec43 = new long[]{-562949953421312L, -8547991553L, -4899916411759099649L, 1979120929931286L};
    static final long[] jjbitVec44 = new long[]{576460743713488896L, -277081220972545L, -1L, 2305629702346244095L};
    static final long[] jjbitVec45 = new long[]{-246290604654592L, 2047L, 562949953421311L, 0L};
    static final long[] jjbitVec46 = new long[]{-864691128455135250L, 281268803551231L, -3186861885341720594L, 4503392135166367L};
    static final long[] jjbitVec47 = new long[]{-3211631683292264476L, 9006925953907079L, -869759877059465234L, 281204393851839L};
    static final long[] jjbitVec48 = new long[]{-878767076314341394L, 281215949093263L, -4341532606274353172L, 280925229301191L};
    static final long[] jjbitVec49 = new long[]{-4327961440926441490L, 281212990012895L, -4327961440926441492L, 281214063754719L};
    static final long[] jjbitVec50 = new long[]{-4323457841299070996L, 281212992110031L, 3457638613854978028L, 3377704004977791L};
    static final long[] jjbitVec51 = new long[]{-8646911284551352322L, 67076095L, 4323434403644581270L, 872365919L};
    static final long[] jjbitVec52 = new long[]{-4422530440275951615L, -554153860399361L, 2305843009196855263L, 64L};
    static final long[] jjbitVec53 = new long[]{272457864671395839L, 67044351L, -4294967296L, 36028797018898495L};
    static final long[] jjbitVec54 = new long[]{-2160230401L, 1123701017804671L, -4294967296L, 9007199254740991L};
    static final long[] jjbitVec55 = new long[]{0L, 0L, -1L, 4393886810111L};
    static final long[] jjbitVec56 = new long[]{-4227893248L, 72057594037927935L, 4398046511103L, 0L};
    static final long[] jjbitVec57 = new long[]{-9223235697412870144L, -9223094959924576255L, 281470681743360L, 9126739968L};
    static final long[] jjbitVec58 = new long[]{522136073208332512L, -2L, -6876561409L, Long.MAX_VALUE};
    static final long[] jjbitVec59 = new long[]{6881498031078244479L, -37L, 1125899906842623L, -524288L};
    static final long[] jjbitVec60 = new long[]{6755463865565184L, -11538275021824000L, -1L, -6917529027641081857L};
    static final long[] jjbitVec61 = new long[]{-8646911293074243568L, -137304735746L, Long.MAX_VALUE, 1008806742219095292L};
    static final int[] jjnextStates = new int[]{
            34, 35, 40, 41, 44, 45, 12, 23, 24, 26,
            14, 16, 49, 51, 6, 8, 9, 12, 23, 24,
            28, 26, 36, 37, 12, 44, 45, 12, 10, 11,
            17, 18, 20, 25, 27, 29, 38, 39, 42, 43,
            46, 47};
    static final long[] jjtoToken = new long[]{-8191L, 2305843009213668639L};
    static final long[] jjtoSkip = new long[]{3646L, 0L};
    static final long[] jjtoSpecial = new long[]{3584L, 0L};
    static final long[] jjtoMore = new long[]{4544L, 0L};
    private static final int[] jjrounds = new int[52];
    private static final int[] jjstateSet = new int[104];
    public static PrintStream debugStream = System.out;
    protected static JavaCharStream input_stream;
    protected static char curChar;
    static StringBuffer image;
    static int jjimageLen;
    static int lengthOfMatch;
    static int curLexState = 0;
    static int defaultLexState = 0;
    static int jjnewStateCnt;
    static int jjround;
    static int jjmatchedPos;
    static int jjmatchedKind;

    public JavaCCParserTokenManager(JavaCharStream stream) {
        if (input_stream != null)
            throw new TokenMgrError("ERROR: Second call to constructor of static lexer. You must use ReInit() to initialize the static variables.", 1);
        input_stream = stream;
    }

    public JavaCCParserTokenManager(JavaCharStream stream, int lexState) {
        this(stream);
        SwitchTo(lexState);
    }

    public static void setDebugStream(PrintStream ds) {
        debugStream = ds;
    }

    private static final int jjStopStringLiteralDfa_0(int pos, long active0, long active1) {
        switch (pos) {
            case 0:
                if ((active0 & 0x140L) != 0L || (active1 & 0x4020000000000L) != 0L)
                    return 2;
                if ((active1 & 0x800004L) != 0L)
                    return 8;
                if ((active0 & 0xFFFFFFFFFFFF6000L) != 0L || (active1 & 0xBL) != 0L) {
                    jjmatchedKind = 76;
                    return 32;
                }
                return -1;
            case 1:
                if ((active0 & 0xFFFFFFDFF3FF6000L) != 0L || (active1 & 0xBL) != 0L) {
                    if (jjmatchedPos != 1) {
                        jjmatchedKind = 76;
                        jjmatchedPos = 1;
                    }
                    return 32;
                }
                if ((active0 & 0x100L) != 0L)
                    return 0;
                if ((active0 & 0x200C000000L) != 0L)
                    return 32;
                return -1;
            case 2:
                if ((active0 & 0xBFFFD9D7FBFF6000L) != 0L || (active1 & 0xBL) != 0L) {
                    if (jjmatchedPos != 2) {
                        jjmatchedKind = 76;
                        jjmatchedPos = 2;
                    }
                    return 32;
                }
                if ((active0 & 0x4000260800000000L) != 0L)
                    return 32;
                return -1;
            case 3:
                if ((active0 & 0x1DFF95C7CBD36000L) != 0L || (active1 & 0xBL) != 0L) {
                    jjmatchedKind = 76;
                    jjmatchedPos = 3;
                    return 32;
                }
                if ((active0 & 0xA2004810302C0000L) != 0L)
                    return 32;
                return -1;
            case 4:
                if ((active0 & 0x11AF95C04B016000L) != 0L || (active1 & 0x9L) != 0L) {
                    if (jjmatchedPos != 4) {
                        jjmatchedKind = 76;
                        jjmatchedPos = 4;
                    }
                    return 32;
                }
                if ((active0 & 0xC50000780D20000L) != 0L || (active1 & 0x2L) != 0L)
                    return 32;
                return -1;
            case 5:
                if ((active0 & 0x1103854243012000L) != 0L || (active1 & 0x9L) != 0L) {
                    jjmatchedKind = 76;
                    jjmatchedPos = 5;
                    return 32;
                }
                if ((active0 & 0x8AC108008004000L) != 0L)
                    return 32;
                return -1;
            case 6:
                if ((active0 & 0x1102054001002000L) != 0L || (active1 & 0x9L) != 0L) {
                    jjmatchedKind = 76;
                    jjmatchedPos = 6;
                    return 32;
                }
                if ((active0 & 0x1800242010000L) != 0L)
                    return 32;
                return -1;
            case 7:
                if ((active0 & 0x1102054000000000L) != 0L) {
                    jjmatchedKind = 76;
                    jjmatchedPos = 7;
                    return 32;
                }
                if ((active0 & 0x1002000L) != 0L || (active1 & 0x9L) != 0L)
                    return 32;
                return -1;
            case 8:
                if ((active0 & 0x100014000000000L) != 0L) {
                    jjmatchedKind = 76;
                    jjmatchedPos = 8;
                    return 32;
                }
                if ((active0 & 0x1002040000000000L) != 0L)
                    return 32;
                return -1;
            case 9:
                if ((active0 & 0x100000000000000L) != 0L) {
                    jjmatchedKind = 76;
                    jjmatchedPos = 9;
                    return 32;
                }
                if ((active0 & 0x14000000000L) != 0L)
                    return 32;
                return -1;
            case 10:
                if ((active0 & 0x100000000000000L) != 0L) {
                    jjmatchedKind = 76;
                    jjmatchedPos = 10;
                    return 32;
                }
                return -1;
        }
        return -1;
    }

    private static final int jjStartNfa_0(int pos, long active0, long active1) {
        return jjMoveNfa_0(jjStopStringLiteralDfa_0(pos, active0, active1), pos + 1);
    }

    private static final int jjStopAtPos(int pos, int kind) {
        jjmatchedKind = kind;
        jjmatchedPos = pos;
        return pos + 1;
    }

    private static final int jjStartNfaWithStates_0(int pos, int kind, int state) {
        jjmatchedKind = kind;
        jjmatchedPos = pos;
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            return pos + 1;
        }
        return jjMoveNfa_0(state, pos + 1);
    }

    private static final int jjMoveStringLiteralDfa0_0() {
        switch (curChar) {
            case '!':
                jjmatchedKind = 90;
                return jjMoveStringLiteralDfa1_0(0L, 8589934592L);
            case '%':
                jjmatchedKind = 109;
                return jjMoveStringLiteralDfa1_0(0L, 18014398509481984L);
            case '&':
                jjmatchedKind = 106;
                return jjMoveStringLiteralDfa1_0(0L, 2251834173423616L);
            case '(':
                return jjStopAtPos(0, 79);
            case ')':
                return jjStopAtPos(0, 80);
            case '*':
                jjmatchedKind = 104;
                return jjMoveStringLiteralDfa1_0(0L, 562949953421312L);
            case '+':
                jjmatchedKind = 102;
                return jjMoveStringLiteralDfa1_0(0L, 140806207832064L);
            case ',':
                return jjStopAtPos(0, 86);
            case '-':
                jjmatchedKind = 103;
                return jjMoveStringLiteralDfa1_0(0L, 281612415664128L);
            case '.':
                jjmatchedKind = 87;
                return jjMoveStringLiteralDfa1_0(0L, 4L);
            case '/':
                jjmatchedKind = 105;
                return jjMoveStringLiteralDfa1_0(320L, 1125899906842624L);
            case ':':
                return jjStopAtPos(0, 93);
            case ';':
                return jjStopAtPos(0, 85);
            case '<':
                jjmatchedKind = 89;
                return jjMoveStringLiteralDfa1_0(0L, 36099167910625280L);
            case '=':
                jjmatchedKind = 88;
                return jjMoveStringLiteralDfa1_0(0L, 1073741824L);
            case '>':
                jjmatchedKind = 124;
                return jjMoveStringLiteralDfa1_0(0L, 1080863914863886336L);
            case '?':
                return jjStopAtPos(0, 92);
            case '@':
                return jjStopAtPos(0, 15);
            case '[':
                return jjStopAtPos(0, 83);
            case ']':
                return jjStopAtPos(0, 84);
            case '^':
                jjmatchedKind = 108;
                return jjMoveStringLiteralDfa1_0(0L, 9007199254740992L);
            case 'a':
                return jjMoveStringLiteralDfa1_0(24576L, 0L);
            case 'b':
                return jjMoveStringLiteralDfa1_0(458752L, 0L);
            case 'c':
                return jjMoveStringLiteralDfa1_0(33030144L, 0L);
            case 'd':
                return jjMoveStringLiteralDfa1_0(234881024L, 0L);
            case 'e':
                return jjMoveStringLiteralDfa1_0(1879048192L, 0L);
            case 'f':
                return jjMoveStringLiteralDfa1_0(66571993088L, 0L);
            case 'g':
                return jjMoveStringLiteralDfa1_0(68719476736L, 0L);
            case 'i':
                return jjMoveStringLiteralDfa1_0(8658654068736L, 0L);
            case 'l':
                return jjMoveStringLiteralDfa1_0(8796093022208L, 0L);
            case 'n':
                return jjMoveStringLiteralDfa1_0(123145302310912L, 0L);
            case 'p':
                return jjMoveStringLiteralDfa1_0(2111062325329920L, 0L);
            case 'r':
                return jjMoveStringLiteralDfa1_0(2251799813685248L, 0L);
            case 's':
                return jjMoveStringLiteralDfa1_0(139611588448485376L, 8L);
            case 't':
                return jjMoveStringLiteralDfa1_0(9079256848778919936L, 0L);
            case 'v':
                return jjMoveStringLiteralDfa1_0(Long.MIN_VALUE, 1L);
            case 'w':
                return jjMoveStringLiteralDfa1_0(0L, 2L);
            case '{':
                return jjStopAtPos(0, 81);
            case '|':
                jjmatchedKind = 107;
                return jjMoveStringLiteralDfa1_0(0L, 4503616807239680L);
            case '}':
                return jjStopAtPos(0, 82);
            case '~':
                return jjStopAtPos(0, 91);
        }
        return jjMoveNfa_0(3, 0);
    }

    private static final int jjMoveStringLiteralDfa1_0(long active0, long active1) {
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(0, active0, active1);
            return 1;
        }
        switch (curChar) {
            case '&':
                if ((active1 & 0x800000000L) != 0L)
                    return jjStopAtPos(1, 99);
                break;
            case '*':
                if ((active0 & 0x100L) != 0L)
                    return jjStartNfaWithStates_0(1, 8, 0);
                break;
            case '+':
                if ((active1 & 0x1000000000L) != 0L)
                    return jjStopAtPos(1, 100);
                break;
            case '-':
                if ((active1 & 0x2000000000L) != 0L)
                    return jjStopAtPos(1, 101);
                break;
            case '.':
                return jjMoveStringLiteralDfa2_0(active0, 0L, active1, 4L);
            case '/':
                if ((active0 & 0x40L) != 0L)
                    return jjStopAtPos(1, 6);
                break;
            case '<':
                if ((active1 & 0x400000000000L) != 0L) {
                    jjmatchedKind = 110;
                    jjmatchedPos = 1;
                }
                return jjMoveStringLiteralDfa2_0(active0, 0L, active1, 36028797018963968L);
            case '=':
                if ((active1 & 0x40000000L) != 0L)
                    return jjStopAtPos(1, 94);
                if ((active1 & 0x80000000L) != 0L)
                    return jjStopAtPos(1, 95);
                if ((active1 & 0x100000000L) != 0L)
                    return jjStopAtPos(1, 96);
                if ((active1 & 0x200000000L) != 0L)
                    return jjStopAtPos(1, 97);
                if ((active1 & 0x800000000000L) != 0L)
                    return jjStopAtPos(1, 111);
                if ((active1 & 0x1000000000000L) != 0L)
                    return jjStopAtPos(1, 112);
                if ((active1 & 0x2000000000000L) != 0L)
                    return jjStopAtPos(1, 113);
                if ((active1 & 0x4000000000000L) != 0L)
                    return jjStopAtPos(1, 114);
                if ((active1 & 0x8000000000000L) != 0L)
                    return jjStopAtPos(1, 115);
                if ((active1 & 0x10000000000000L) != 0L)
                    return jjStopAtPos(1, 116);
                if ((active1 & 0x20000000000000L) != 0L)
                    return jjStopAtPos(1, 117);
                if ((active1 & 0x40000000000000L) != 0L)
                    return jjStopAtPos(1, 118);
                break;
            case '>':
                if ((active1 & 0x800000000000000L) != 0L) {
                    jjmatchedKind = 123;
                    jjmatchedPos = 1;
                }
                return jjMoveStringLiteralDfa2_0(active0, 0L, active1, 504403158265495552L);
            case 'a':
                return jjMoveStringLiteralDfa2_0(active0, 158331823456256L, active1, 0L);
            case 'b':
                return jjMoveStringLiteralDfa2_0(active0, 8192L, active1, 0L);
            case 'e':
                return jjMoveStringLiteralDfa2_0(active0, 2286984219328512L, active1, 0L);
            case 'f':
                if ((active0 & 0x2000000000L) != 0L)
                    return jjStartNfaWithStates_0(1, 37, 32);
                break;
            case 'h':
                return jjMoveStringLiteralDfa2_0(active0, 1013309916160458752L, active1, 2L);
            case 'i':
                return jjMoveStringLiteralDfa2_0(active0, 12884901888L, active1, 0L);
            case 'l':
                return jjMoveStringLiteralDfa2_0(active0, 17452498944L, active1, 0L);
            case 'm':
                return jjMoveStringLiteralDfa2_0(active0, 824633720832L, active1, 0L);
            case 'n':
                return jjMoveStringLiteralDfa2_0(active0, 7697118265344L, active1, 0L);
            case 'o':
                if ((active0 & 0x4000000L) != 0L) {
                    jjmatchedKind = 26;
                    jjmatchedPos = 1;
                }
                return jjMoveStringLiteralDfa2_0(active0, -9223363137523089408L, active1, 1L);
            case 'r':
                return jjMoveStringLiteralDfa2_0(active0, 8071294957178191872L, active1, 0L);
            case 's':
                return jjMoveStringLiteralDfa2_0(active0, 16384L, active1, 0L);
            case 't':
                return jjMoveStringLiteralDfa2_0(active0, 9007199254740992L, active1, 8L);
            case 'u':
                return jjMoveStringLiteralDfa2_0(active0, 19210667160502272L, active1, 0L);
            case 'w':
                return jjMoveStringLiteralDfa2_0(active0, 36028797018963968L, active1, 0L);
            case 'x':
                return jjMoveStringLiteralDfa2_0(active0, 1073741824L, active1, 0L);
            case 'y':
                return jjMoveStringLiteralDfa2_0(active0, 72057594038190080L, active1, 0L);
            case '|':
                if ((active1 & 0x400000000L) != 0L)
                    return jjStopAtPos(1, 98);
                break;
        }
        return jjStartNfa_0(0, active0, active1);
    }

    private static final int jjMoveStringLiteralDfa2_0(long old0, long active0, long old1, long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L)
            return jjStartNfa_0(0, old0, old1);
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(1, active0, active1);
            return 2;
        }
        switch (curChar) {
            case '.':
                if ((active1 & 0x4L) != 0L)
                    return jjStopAtPos(2, 66);
                break;
            case '=':
                if ((active1 & 0x80000000000000L) != 0L)
                    return jjStopAtPos(2, 119);
                if ((active1 & 0x100000000000000L) != 0L)
                    return jjStopAtPos(2, 120);
                break;
            case '>':
                if ((active1 & 0x400000000000000L) != 0L) {
                    jjmatchedKind = 122;
                    jjmatchedPos = 2;
                }
                return jjMoveStringLiteralDfa3_0(active0, 0L, active1, 144115188075855872L);
            case 'a':
                return jjMoveStringLiteralDfa3_0(active0, 1161928703867879424L, active1, 0L);
            case 'b':
                return jjMoveStringLiteralDfa3_0(active0, 1125899906842624L, active1, 0L);
            case 'c':
                return jjMoveStringLiteralDfa3_0(active0, 140737488355328L, active1, 0L);
            case 'e':
                return jjMoveStringLiteralDfa3_0(active0, 131072L, active1, 0L);
            case 'f':
                return jjMoveStringLiteralDfa3_0(active0, 33554432L, active1, 0L);
            case 'i':
                return jjMoveStringLiteralDfa3_0(active0, -9042946576783245312L, active1, 2L);
            case 'l':
                return jjMoveStringLiteralDfa3_0(active0, 70370891661312L, active1, 1L);
            case 'n':
                return jjMoveStringLiteralDfa3_0(active0, 72066403041017856L, active1, 0L);
            case 'o':
                return jjMoveStringLiteralDfa3_0(active0, 5066566760726528L, active1, 0L);
            case 'p':
                return jjMoveStringLiteralDfa3_0(active0, 18015223143202816L, active1, 0L);
            case 'r':
                if ((active0 & 0x800000000L) != 0L)
                    return jjStartNfaWithStates_0(2, 35, 32);
                return jjMoveStringLiteralDfa3_0(active0, 864691128455135232L, active1, 8L);
            case 's':
                return jjMoveStringLiteralDfa3_0(active0, 1099780612096L, active1, 0L);
            case 't':
                if ((active0 & 0x20000000000L) != 0L) {
                    jjmatchedKind = 41;
                    jjmatchedPos = 2;
                }
                return jjMoveStringLiteralDfa3_0(active0, 2273859840770048L, active1, 0L);
            case 'u':
                return jjMoveStringLiteralDfa3_0(active0, 2305843009884782592L, active1, 0L);
            case 'w':
                if ((active0 & 0x200000000000L) != 0L)
                    return jjStartNfaWithStates_0(2, 45, 32);
                break;
            case 'y':
                if ((active0 & 0x4000000000000000L) != 0L)
                    return jjStartNfaWithStates_0(2, 62, 32);
                break;
        }
        return jjStartNfa_0(1, active0, active1);
    }

    private static final int jjMoveStringLiteralDfa3_0(long old0, long active0, long old1, long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L)
            return jjStartNfa_0(1, old0, old1);
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(2, active0, active1);
            return 3;
        }
        switch (curChar) {
            case '=':
                if ((active1 & 0x200000000000000L) != 0L)
                    return jjStopAtPos(3, 121);
                break;
            case 'a':
                return jjMoveStringLiteralDfa4_0(active0, 30098456576L, active1, 1L);
            case 'b':
                return jjMoveStringLiteralDfa4_0(active0, 134217728L, active1, 0L);
            case 'c':
                return jjMoveStringLiteralDfa4_0(active0, 72057594038976512L, active1, 0L);
            case 'd':
                if ((active0 & Long.MIN_VALUE) != 0L)
                    return jjStartNfaWithStates_0(3, 63, 32);
                break;
            case 'e':
                if ((active0 & 0x40000L) != 0L)
                    return jjStartNfaWithStates_0(3, 18, 32);
                if ((active0 & 0x80000L) != 0L)
                    return jjStartNfaWithStates_0(3, 19, 32);
                if ((active0 & 0x10000000L) != 0L)
                    return jjStartNfaWithStates_0(3, 28, 32);
                if ((active0 & 0x2000000000000000L) != 0L)
                    return jjStartNfaWithStates_0(3, 61, 32);
                return jjMoveStringLiteralDfa4_0(active0, 18018797629751296L, active1, 0L);
            case 'g':
                if ((active0 & 0x80000000000L) != 0L)
                    return jjStartNfaWithStates_0(3, 43, 32);
                break;
            case 'i':
                return jjMoveStringLiteralDfa4_0(active0, 17592186044416L, active1, 8L);
            case 'k':
                return jjMoveStringLiteralDfa4_0(active0, 140737488355328L, active1, 0L);
            case 'l':
                if ((active0 & 0x400000000000L) != 0L)
                    return jjStartNfaWithStates_0(3, 46, 32);
                return jjMoveStringLiteralDfa4_0(active0, 1126174784815104L, active1, 2L);
            case 'm':
                if ((active0 & 0x20000000L) != 0L)
                    return jjStartNfaWithStates_0(3, 29, 32);
                break;
            case 'n':
                return jjMoveStringLiteralDfa4_0(active0, 1152921504606846976L, active1, 0L);
            case 'o':
                if ((active0 & 0x1000000000L) != 0L)
                    return jjStartNfaWithStates_0(3, 36, 32);
                return jjMoveStringLiteralDfa4_0(active0, 864691678210949120L, active1, 0L);
            case 'r':
                if ((active0 & 0x200000L) != 0L)
                    return jjStartNfaWithStates_0(3, 21, 32);
                return jjMoveStringLiteralDfa4_0(active0, 4503599627370496L, active1, 0L);
            case 's':
                if ((active0 & 0x200000000000000L) != 0L)
                    return jjStartNfaWithStates_0(3, 57, 32);
                return jjMoveStringLiteralDfa4_0(active0, 2160066560L, active1, 0L);
            case 't':
                return jjMoveStringLiteralDfa4_0(active0, 45600045755539456L, active1, 0L);
            case 'u':
                return jjMoveStringLiteralDfa4_0(active0, 2251799813685248L, active1, 0L);
            case 'v':
                return jjMoveStringLiteralDfa4_0(active0, 281474976710656L, active1, 0L);
        }
        return jjStartNfa_0(2, active0, active1);
    }

    private static final int jjMoveStringLiteralDfa4_0(long old0, long active0, long old1, long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L)
            return jjStartNfa_0(2, old0, old1);
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(3, active0, active1);
            return 4;
        }
        switch (curChar) {
            case 'a':
                return jjMoveStringLiteralDfa5_0(active0, 423311976693760L, active1, 0L);
            case 'c':
                return jjMoveStringLiteralDfa5_0(active0, 36028797018963968L, active1, 8L);
            case 'e':
                if ((active0 & 0x80000000L) != 0L)
                    return jjStartNfaWithStates_0(4, 31, 32);
                if ((active1 & 0x2L) != 0L)
                    return jjStartNfaWithStates_0(4, 65, 32);
                return jjMoveStringLiteralDfa5_0(active0, 563224831393792L, active1, 0L);
            case 'h':
                if ((active0 & 0x100000L) != 0L)
                    return jjStartNfaWithStates_0(4, 20, 32);
                return jjMoveStringLiteralDfa5_0(active0, 72057594037927936L, active1, 0L);
            case 'i':
                return jjMoveStringLiteralDfa5_0(active0, 10133099178360832L, active1, 0L);
            case 'k':
                if ((active0 & 0x20000L) != 0L)
                    return jjStartNfaWithStates_0(4, 17, 32);
                break;
            case 'l':
                if ((active0 & 0x100000000L) != 0L) {
                    jjmatchedKind = 32;
                    jjmatchedPos = 4;
                }
                return jjMoveStringLiteralDfa5_0(active0, 8724152320L, active1, 0L);
            case 'n':
                return jjMoveStringLiteralDfa5_0(active0, 1073741824L, active1, 0L);
            case 'r':
                if ((active0 & 0x40000000000000L) != 0L)
                    return jjStartNfaWithStates_0(4, 54, 32);
                return jjMoveStringLiteralDfa5_0(active0, 2256747616034816L, active1, 0L);
            case 's':
                if ((active0 & 0x400000L) != 0L)
                    return jjStartNfaWithStates_0(4, 22, 32);
                return jjMoveStringLiteralDfa5_0(active0, 1152921504606846976L, active1, 0L);
            case 't':
                if ((active0 & 0x800000L) != 0L)
                    return jjStartNfaWithStates_0(4, 23, 32);
                if ((active0 & 0x400000000L) != 0L)
                    return jjStartNfaWithStates_0(4, 34, 32);
                if ((active0 & 0x10000000000000L) != 0L)
                    return jjStartNfaWithStates_0(4, 52, 32);
                return jjMoveStringLiteralDfa5_0(active0, 0L, active1, 1L);
            case 'u':
                return jjMoveStringLiteralDfa5_0(active0, 33554432L, active1, 0L);
            case 'v':
                return jjMoveStringLiteralDfa5_0(active0, 17592186044416L, active1, 0L);
            case 'w':
                if ((active0 & 0x400000000000000L) != 0L) {
                    jjmatchedKind = 58;
                    jjmatchedPos = 4;
                }
                return jjMoveStringLiteralDfa5_0(active0, 576460752303423488L, active1, 0L);
        }
        return jjStartNfa_0(3, active0, active1);
    }

    private static final int jjMoveStringLiteralDfa5_0(long old0, long active0, long old1, long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L)
            return jjStartNfa_0(3, old0, old1);
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(4, active0, active1);
            return 5;
        }
        switch (curChar) {
            case 'a':
                return jjMoveStringLiteralDfa6_0(active0, 73728L, active1, 0L);
            case 'c':
                if ((active0 & 0x4000000000000L) != 0L)
                    return jjStartNfaWithStates_0(5, 50, 32);
                if ((active0 & 0x20000000000000L) != 0L)
                    return jjStartNfaWithStates_0(5, 53, 32);
                return jjMoveStringLiteralDfa6_0(active0, 562949953421312L, active1, 0L);
            case 'd':
                return jjMoveStringLiteralDfa6_0(active0, 1073741824L, active1, 0L);
            case 'e':
                if ((active0 & 0x8000000L) != 0L)
                    return jjStartNfaWithStates_0(5, 27, 32);
                if ((active0 & 0x100000000000L) != 0L)
                    return jjStartNfaWithStates_0(5, 44, 32);
                break;
            case 'f':
                return jjMoveStringLiteralDfa6_0(active0, 4398046511104L, active1, 0L);
            case 'g':
                return jjMoveStringLiteralDfa6_0(active0, 140737488355328L, active1, 0L);
            case 'h':
                if ((active0 & 0x80000000000000L) != 0L)
                    return jjStartNfaWithStates_0(5, 55, 32);
                break;
            case 'i':
                return jjMoveStringLiteralDfa6_0(active0, 1152921504606846976L, active1, 1L);
            case 'l':
                return jjMoveStringLiteralDfa6_0(active0, 8623489024L, active1, 0L);
            case 'm':
                return jjMoveStringLiteralDfa6_0(active0, 274877906944L, active1, 0L);
            case 'n':
                if ((active0 & 0x8000000000000L) != 0L)
                    return jjStartNfaWithStates_0(5, 51, 32);
                return jjMoveStringLiteralDfa6_0(active0, 1099528404992L, active1, 0L);
            case 'r':
                return jjMoveStringLiteralDfa6_0(active0, 72057594037927936L, active1, 0L);
            case 's':
                if ((active0 & 0x800000000000000L) != 0L)
                    return jjStartNfaWithStates_0(5, 59, 32);
                break;
            case 't':
                if ((active0 & 0x4000L) != 0L)
                    return jjStartNfaWithStates_0(5, 14, 32);
                if ((active0 & 0x8000000000L) != 0L)
                    return jjStartNfaWithStates_0(5, 39, 32);
                return jjMoveStringLiteralDfa6_0(active0, 281474976710656L, active1, 8L);
        }
        return jjStartNfa_0(4, active0, active1);
    }

    private static final int jjMoveStringLiteralDfa6_0(long old0, long active0, long old1, long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L)
            return jjStartNfa_0(4, old0, old1);
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(5, active0, active1);
            return 6;
        }
        switch (curChar) {
            case 'a':
                return jjMoveStringLiteralDfa7_0(active0, 4398046511104L, active1, 0L);
            case 'c':
                return jjMoveStringLiteralDfa7_0(active0, 1099511635968L, active1, 0L);
            case 'e':
                if ((active0 & 0x800000000000L) != 0L)
                    return jjStartNfaWithStates_0(6, 47, 32);
                if ((active0 & 0x1000000000000L) != 0L)
                    return jjStartNfaWithStates_0(6, 48, 32);
                return jjMoveStringLiteralDfa7_0(active0, 1152921779484753920L, active1, 0L);
            case 'f':
                return jjMoveStringLiteralDfa7_0(active0, 0L, active1, 8L);
            case 'l':
                return jjMoveStringLiteralDfa7_0(active0, 0L, active1, 1L);
            case 'n':
                if ((active0 & 0x10000L) != 0L)
                    return jjStartNfaWithStates_0(6, 16, 32);
                break;
            case 'o':
                return jjMoveStringLiteralDfa7_0(active0, 72057594037927936L, active1, 0L);
            case 's':
                if ((active0 & 0x40000000L) != 0L)
                    return jjStartNfaWithStates_0(6, 30, 32);
                break;
            case 't':
                if ((active0 & 0x2000000L) != 0L)
                    return jjStartNfaWithStates_0(6, 25, 32);
                return jjMoveStringLiteralDfa7_0(active0, 562949953421312L, active1, 0L);
            case 'u':
                return jjMoveStringLiteralDfa7_0(active0, 16777216L, active1, 0L);
            case 'y':
                if ((active0 & 0x200000000L) != 0L)
                    return jjStartNfaWithStates_0(6, 33, 32);
                break;
        }
        return jjStartNfa_0(5, active0, active1);
    }

    private static final int jjMoveStringLiteralDfa7_0(long old0, long active0, long old1, long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L)
            return jjStartNfa_0(5, old0, old1);
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(6, active0, active1);
            return 7;
        }
        switch (curChar) {
            case 'c':
                return jjMoveStringLiteralDfa8_0(active0, 4398046511104L, active1, 0L);
            case 'e':
                if ((active0 & 0x1000000L) != 0L)
                    return jjStartNfaWithStates_0(7, 24, 32);
                if ((active1 & 0x1L) != 0L)
                    return jjStartNfaWithStates_0(7, 64, 32);
                return jjMoveStringLiteralDfa8_0(active0, 564049465049088L, active1, 0L);
            case 'n':
                return jjMoveStringLiteralDfa8_0(active0, 1224979373522681856L, active1, 0L);
            case 'p':
                if ((active1 & 0x8L) != 0L)
                    return jjStartNfaWithStates_0(7, 67, 32);
                break;
            case 't':
                if ((active0 & 0x2000L) != 0L)
                    return jjStartNfaWithStates_0(7, 13, 32);
                break;
        }
        return jjStartNfa_0(6, active0, active1);
    }

    private static final int jjMoveStringLiteralDfa8_0(long old0, long active0, long old1, long active1) {
        if (((active0 &= old0) | (active1 &= old1)) == 0L)
            return jjStartNfa_0(6, old0, old1);
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(7, active0, 0L);
            return 8;
        }
        switch (curChar) {
            case 'd':
                if ((active0 & 0x2000000000000L) != 0L)
                    return jjStartNfaWithStates_0(8, 49, 32);
                break;
            case 'e':
                if ((active0 & 0x40000000000L) != 0L)
                    return jjStartNfaWithStates_0(8, 42, 32);
                break;
            case 'i':
                return jjMoveStringLiteralDfa9_0(active0, 72057594037927936L);
            case 'o':
                return jjMoveStringLiteralDfa9_0(active0, 1099511627776L);
            case 't':
                if ((active0 & 0x1000000000000000L) != 0L)
                    return jjStartNfaWithStates_0(8, 60, 32);
                return jjMoveStringLiteralDfa9_0(active0, 274877906944L);
        }
        return jjStartNfa_0(7, active0, 0L);
    }

    private static final int jjMoveStringLiteralDfa9_0(long old0, long active0) {
        if ((active0 &= old0) == 0L)
            return jjStartNfa_0(7, old0, 0L);
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(8, active0, 0L);
            return 9;
        }
        switch (curChar) {
            case 'f':
                if ((active0 & 0x10000000000L) != 0L)
                    return jjStartNfaWithStates_0(9, 40, 32);
                break;
            case 's':
                if ((active0 & 0x4000000000L) != 0L)
                    return jjStartNfaWithStates_0(9, 38, 32);
                break;
            case 'z':
                return jjMoveStringLiteralDfa10_0(active0, 72057594037927936L);
        }
        return jjStartNfa_0(8, active0, 0L);
    }

    private static final int jjMoveStringLiteralDfa10_0(long old0, long active0) {
        if ((active0 &= old0) == 0L)
            return jjStartNfa_0(8, old0, 0L);
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(9, active0, 0L);
            return 10;
        }
        switch (curChar) {
            case 'e':
                return jjMoveStringLiteralDfa11_0(active0, 72057594037927936L);
        }
        return jjStartNfa_0(9, active0, 0L);
    }

    private static final int jjMoveStringLiteralDfa11_0(long old0, long active0) {
        if ((active0 &= old0) == 0L)
            return jjStartNfa_0(9, old0, 0L);
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            jjStopStringLiteralDfa_0(10, active0, 0L);
            return 11;
        }
        switch (curChar) {
            case 'd':
                if ((active0 & 0x100000000000000L) != 0L)
                    return jjStartNfaWithStates_0(11, 56, 32);
                break;
        }
        return jjStartNfa_0(10, active0, 0L);
    }

    private static final void jjCheckNAdd(int state) {
        if (jjrounds[state] != jjround) {
            jjstateSet[jjnewStateCnt++] = state;
            jjrounds[state] = jjround;
        }
    }

    private static final void jjAddStates(int start, int end) {
        do {
            jjstateSet[jjnewStateCnt++] = jjnextStates[start];
        } while (start++ != end);
    }

    private static final void jjCheckNAddTwoStates(int state1, int state2) {
        jjCheckNAdd(state1);
        jjCheckNAdd(state2);
    }

    private static final void jjCheckNAddStates(int start, int end) {
        do {
            jjCheckNAdd(jjnextStates[start]);
        } while (start++ != end);
    }

    private static final void jjCheckNAddStates(int start) {
        jjCheckNAdd(jjnextStates[start]);
        jjCheckNAdd(jjnextStates[start + 1]);
    }

    private static final int jjMoveNfa_0(int startState, int curPos) {
        int startsAt = 0;
        jjnewStateCnt = 52;
        int i = 1;
        jjstateSet[0] = startState;
        int kind = Integer.MAX_VALUE;
        while (true) {
            if (++jjround == Integer.MAX_VALUE)
                ReInitRounds();
            if (curChar < '@') {
                long l = 1L << curChar;
                do {
                    switch (jjstateSet[--i]) {
                        case 3:
                            if ((0x3FF000000000000L & l) != 0L) {
                                jjCheckNAddStates(0, 6);
                            } else if (curChar == '$') {
                                if (kind > 76)
                                    kind = 76;
                                jjCheckNAdd(32);
                            } else if (curChar == '"') {
                                jjCheckNAddStates(7, 9);
                            } else if (curChar == '\'') {
                                jjAddStates(10, 11);
                            } else if (curChar == '.') {
                                jjCheckNAdd(8);
                            } else if (curChar == '/') {
                                jjstateSet[jjnewStateCnt++] = 2;
                            }
                            if ((0x3FE000000000000L & l) != 0L) {
                                if (kind > 68)
                                    kind = 68;
                                jjCheckNAddTwoStates(5, 6);
                                break;
                            }
                            if (curChar == '0') {
                                if (kind > 68)
                                    kind = 68;
                                jjCheckNAddStates(12, 14);
                            }
                            break;
                        case 0:
                            if (curChar == '*')
                                jjstateSet[jjnewStateCnt++] = 1;
                            break;
                        case 1:
                            if ((0xFFFF7FFFFFFFFFFFL & l) != 0L && kind > 7)
                                kind = 7;
                            break;
                        case 2:
                            if (curChar == '*')
                                jjstateSet[jjnewStateCnt++] = 0;
                            break;
                        case 4:
                            if ((0x3FE000000000000L & l) == 0L)
                                break;
                            if (kind > 68)
                                kind = 68;
                            jjCheckNAddTwoStates(5, 6);
                            break;
                        case 5:
                            if ((0x3FF000000000000L & l) == 0L)
                                break;
                            if (kind > 68)
                                kind = 68;
                            jjCheckNAddTwoStates(5, 6);
                            break;
                        case 7:
                            if (curChar == '.')
                                jjCheckNAdd(8);
                            break;
                        case 8:
                            if ((0x3FF000000000000L & l) == 0L)
                                break;
                            if (kind > 72)
                                kind = 72;
                            jjCheckNAddStates(15, 17);
                            break;
                        case 10:
                            if ((0x280000000000L & l) != 0L)
                                jjCheckNAdd(11);
                            break;
                        case 11:
                            if ((0x3FF000000000000L & l) == 0L)
                                break;
                            if (kind > 72)
                                kind = 72;
                            jjCheckNAddTwoStates(11, 12);
                            break;
                        case 13:
                            if (curChar == '\'')
                                jjAddStates(10, 11);
                            break;
                        case 14:
                            if ((0xFFFFFF7FFFFFDBFFL & l) != 0L)
                                jjCheckNAdd(15);
                            break;
                        case 15:
                            if (curChar == '\'' && kind > 74)
                                kind = 74;
                            break;
                        case 17:
                            if ((0x8400000000L & l) != 0L)
                                jjCheckNAdd(15);
                            break;
                        case 18:
                            if ((0xFF000000000000L & l) != 0L)
                                jjCheckNAddTwoStates(19, 15);
                            break;
                        case 19:
                            if ((0xFF000000000000L & l) != 0L)
                                jjCheckNAdd(15);
                            break;
                        case 20:
                            if ((0xF000000000000L & l) != 0L)
                                jjstateSet[jjnewStateCnt++] = 21;
                            break;
                        case 21:
                            if ((0xFF000000000000L & l) != 0L)
                                jjCheckNAdd(19);
                            break;
                        case 22:
                            if (curChar == '"')
                                jjCheckNAddStates(7, 9);
                            break;
                        case 23:
                            if ((0xFFFFFFFBFFFFDBFFL & l) != 0L)
                                jjCheckNAddStates(7, 9);
                            break;
                        case 25:
                            if ((0x8400000000L & l) != 0L)
                                jjCheckNAddStates(7, 9);
                            break;
                        case 26:
                            if (curChar == '"' && kind > 75)
                                kind = 75;
                            break;
                        case 27:
                            if ((0xFF000000000000L & l) != 0L)
                                jjCheckNAddStates(18, 21);
                            break;
                        case 28:
                            if ((0xFF000000000000L & l) != 0L)
                                jjCheckNAddStates(7, 9);
                            break;
                        case 29:
                            if ((0xF000000000000L & l) != 0L)
                                jjstateSet[jjnewStateCnt++] = 30;
                            break;
                        case 30:
                            if ((0xFF000000000000L & l) != 0L)
                                jjCheckNAdd(28);
                            break;
                        case 31:
                            if (curChar != '$')
                                break;
                            if (kind > 76)
                                kind = 76;
                            jjCheckNAdd(32);
                            break;
                        case 32:
                            if ((0x3FF00100FFFC1FFL & l) == 0L)
                                break;
                            if (kind > 76)
                                kind = 76;
                            jjCheckNAdd(32);
                            break;
                        case 33:
                            if ((0x3FF000000000000L & l) != 0L)
                                jjCheckNAddStates(0, 6);
                            break;
                        case 34:
                            if ((0x3FF000000000000L & l) != 0L)
                                jjCheckNAddTwoStates(34, 35);
                            break;
                        case 35:
                            if (curChar != '.')
                                break;
                            if (kind > 72)
                                kind = 72;
                            jjCheckNAddStates(22, 24);
                            break;
                        case 36:
                            if ((0x3FF000000000000L & l) == 0L)
                                break;
                            if (kind > 72)
                                kind = 72;
                            jjCheckNAddStates(22, 24);
                            break;
                        case 38:
                            if ((0x280000000000L & l) != 0L)
                                jjCheckNAdd(39);
                            break;
                        case 39:
                            if ((0x3FF000000000000L & l) == 0L)
                                break;
                            if (kind > 72)
                                kind = 72;
                            jjCheckNAddTwoStates(39, 12);
                            break;
                        case 40:
                            if ((0x3FF000000000000L & l) != 0L)
                                jjCheckNAddTwoStates(40, 41);
                            break;
                        case 42:
                            if ((0x280000000000L & l) != 0L)
                                jjCheckNAdd(43);
                            break;
                        case 43:
                            if ((0x3FF000000000000L & l) == 0L)
                                break;
                            if (kind > 72)
                                kind = 72;
                            jjCheckNAddTwoStates(43, 12);
                            break;
                        case 44:
                            if ((0x3FF000000000000L & l) != 0L)
                                jjCheckNAddStates(25, 27);
                            break;
                        case 46:
                            if ((0x280000000000L & l) != 0L)
                                jjCheckNAdd(47);
                            break;
                        case 47:
                            if ((0x3FF000000000000L & l) != 0L)
                                jjCheckNAddTwoStates(47, 12);
                            break;
                        case 48:
                            if (curChar != '0')
                                break;
                            if (kind > 68)
                                kind = 68;
                            jjCheckNAddStates(12, 14);
                            break;
                        case 50:
                            if ((0x3FF000000000000L & l) == 0L)
                                break;
                            if (kind > 68)
                                kind = 68;
                            jjCheckNAddTwoStates(50, 6);
                            break;
                        case 51:
                            if ((0xFF000000000000L & l) == 0L)
                                break;
                            if (kind > 68)
                                kind = 68;
                            jjCheckNAddTwoStates(51, 6);
                            break;
                    }
                } while (i != startsAt);
            } else if (curChar < '\u0080') {
                long l = 1L << (curChar & 0x3F);
                do {
                    switch (jjstateSet[--i]) {
                        case 3:
                            if ((0x7FFFFFE87FFFFFEL & l) == 0L)
                                break;
                            if (kind > 76)
                                kind = 76;
                            jjCheckNAdd(32);
                            break;
                        case 1:
                            if (kind > 7)
                                kind = 7;
                            break;
                        case 6:
                            if ((0x100000001000L & l) != 0L && kind > 68)
                                kind = 68;
                            break;
                        case 9:
                            if ((0x2000000020L & l) != 0L)
                                jjAddStates(28, 29);
                            break;
                        case 12:
                            if ((0x5000000050L & l) != 0L && kind > 72)
                                kind = 72;
                            break;
                        case 14:
                            if ((0xFFFFFFFFEFFFFFFFL & l) != 0L)
                                jjCheckNAdd(15);
                            break;
                        case 16:
                            if (curChar == '\\')
                                jjAddStates(30, 32);
                            break;
                        case 17:
                            if ((0x14404410000000L & l) != 0L)
                                jjCheckNAdd(15);
                            break;
                        case 23:
                            if ((0xFFFFFFFFEFFFFFFFL & l) != 0L)
                                jjCheckNAddStates(7, 9);
                            break;
                        case 24:
                            if (curChar == '\\')
                                jjAddStates(33, 35);
                            break;
                        case 25:
                            if ((0x14404410000000L & l) != 0L)
                                jjCheckNAddStates(7, 9);
                            break;
                        case 32:
                            if ((0x87FFFFFE87FFFFFEL & l) == 0L)
                                break;
                            if (kind > 76)
                                kind = 76;
                            jjCheckNAdd(32);
                            break;
                        case 37:
                            if ((0x2000000020L & l) != 0L)
                                jjAddStates(36, 37);
                            break;
                        case 41:
                            if ((0x2000000020L & l) != 0L)
                                jjAddStates(38, 39);
                            break;
                        case 45:
                            if ((0x2000000020L & l) != 0L)
                                jjAddStates(40, 41);
                            break;
                        case 49:
                            if ((0x100000001000000L & l) != 0L)
                                jjCheckNAdd(50);
                            break;
                        case 50:
                            if ((0x7E0000007EL & l) == 0L)
                                break;
                            if (kind > 68)
                                kind = 68;
                            jjCheckNAddTwoStates(50, 6);
                            break;
                    }
                } while (i != startsAt);
            } else {
                int hiByte = curChar >> 8;
                int i1 = hiByte >> 6;
                long l1 = 1L << (hiByte & 0x3F);
                int i2 = (curChar & 0xFF) >> 6;
                long l2 = 1L << (curChar & 0x3F);
                do {
                    switch (jjstateSet[--i]) {
                        case 3:
                            if (!jjCanMove_1(hiByte, i1, i2, l1, l2))
                                break;
                            if (kind > 76)
                                kind = 76;
                            jjCheckNAdd(32);
                            break;
                        case 1:
                            if (jjCanMove_0(hiByte, i1, i2, l1, l2) && kind > 7)
                                kind = 7;
                            break;
                        case 14:
                            if (jjCanMove_0(hiByte, i1, i2, l1, l2))
                                jjstateSet[jjnewStateCnt++] = 15;
                            break;
                        case 23:
                            if (jjCanMove_0(hiByte, i1, i2, l1, l2))
                                jjAddStates(7, 9);
                            break;
                        case 32:
                            if (!jjCanMove_2(hiByte, i1, i2, l1, l2))
                                break;
                            if (kind > 76)
                                kind = 76;
                            jjCheckNAdd(32);
                            break;
                    }
                } while (i != startsAt);
            }
            if (kind != Integer.MAX_VALUE) {
                jjmatchedKind = kind;
                jjmatchedPos = curPos;
                kind = Integer.MAX_VALUE;
            }
            curPos++;
            if ((i = jjnewStateCnt) == (startsAt = 52 - (jjnewStateCnt = startsAt)))
                return curPos;
            try {
                curChar = JavaCharStream.readChar();
            } catch (IOException e) {
                return curPos;
            }
        }
    }

    private static final int jjMoveStringLiteralDfa0_3() {
        switch (curChar) {
            case '*':
                return jjMoveStringLiteralDfa1_3(2048L);
        }
        return 1;
    }

    private static final int jjMoveStringLiteralDfa1_3(long active0) {
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            return 1;
        }
        switch (curChar) {
            case '/':
                if ((active0 & 0x800L) != 0L)
                    return jjStopAtPos(1, 11);
                return 2;
        }
        return 2;
    }

    private static final int jjMoveStringLiteralDfa0_1() {
        return jjMoveNfa_1(0, 0);
    }

    private static final int jjMoveNfa_1(int startState, int curPos) {
        int startsAt = 0;
        jjnewStateCnt = 3;
        int i = 1;
        jjstateSet[0] = startState;
        int kind = Integer.MAX_VALUE;
        while (true) {
            if (++jjround == Integer.MAX_VALUE)
                ReInitRounds();
            if (curChar < '@') {
                long l = 1L << curChar;
                do {
                    switch (jjstateSet[--i]) {
                        case 0:
                            if ((0x2400L & l) != 0L)
                                if (kind > 9)
                                    kind = 9;
                            if (curChar == '\r')
                                jjstateSet[jjnewStateCnt++] = 1;
                            break;
                        case 1:
                            if (curChar == '\n' && kind > 9)
                                kind = 9;
                            break;
                        case 2:
                            if (curChar == '\r')
                                jjstateSet[jjnewStateCnt++] = 1;
                            break;
                    }
                } while (i != startsAt);
            } else if (curChar < '\u0080') {
                long l = 1L << (curChar & 0x3F);
                do {
                    switch (jjstateSet[--i]) {

                    }
                } while (i != startsAt);
            } else {
                int hiByte = curChar >> 8;
                int i1 = hiByte >> 6;
                long l1 = 1L << (hiByte & 0x3F);
                int i2 = (curChar & 0xFF) >> 6;
                long l2 = 1L << (curChar & 0x3F);
                do {
                    switch (jjstateSet[--i]) {

                    }
                } while (i != startsAt);
            }
            if (kind != Integer.MAX_VALUE) {
                jjmatchedKind = kind;
                jjmatchedPos = curPos;
                kind = Integer.MAX_VALUE;
            }
            curPos++;
            if ((i = jjnewStateCnt) == (startsAt = 3 - (jjnewStateCnt = startsAt)))
                return curPos;
            try {
                curChar = JavaCharStream.readChar();
            } catch (IOException e) {
                return curPos;
            }
        }
    }

    private static final int jjMoveStringLiteralDfa0_2() {
        switch (curChar) {
            case '*':
                return jjMoveStringLiteralDfa1_2(1024L);
        }
        return 1;
    }

    private static final int jjMoveStringLiteralDfa1_2(long active0) {
        try {
            curChar = JavaCharStream.readChar();
        } catch (IOException e) {
            return 1;
        }
        switch (curChar) {
            case '/':
                if ((active0 & 0x400L) != 0L)
                    return jjStopAtPos(1, 10);
                return 2;
        }
        return 2;
    }

    private static final boolean jjCanMove_0(int hiByte, int i1, int i2, long l1, long l2) {
        switch (hiByte) {
            case 0:
                return ((jjbitVec2[i2] & l2) != 0L);
        }
        return (jjbitVec0[i1] & l1) != 0L;
    }

    private static final boolean jjCanMove_1(int hiByte, int i1, int i2, long l1, long l2) {
        switch (hiByte) {
            case 0:
                return ((jjbitVec4[i2] & l2) != 0L);
            case 2:
                return ((jjbitVec5[i2] & l2) != 0L);
            case 3:
                return ((jjbitVec6[i2] & l2) != 0L);
            case 4:
                return ((jjbitVec7[i2] & l2) != 0L);
            case 5:
                return ((jjbitVec8[i2] & l2) != 0L);
            case 6:
                return ((jjbitVec9[i2] & l2) != 0L);
            case 7:
                return ((jjbitVec10[i2] & l2) != 0L);
            case 9:
                return ((jjbitVec11[i2] & l2) != 0L);
            case 10:
                return ((jjbitVec12[i2] & l2) != 0L);
            case 11:
                return ((jjbitVec13[i2] & l2) != 0L);
            case 12:
                return ((jjbitVec14[i2] & l2) != 0L);
            case 13:
                return ((jjbitVec15[i2] & l2) != 0L);
            case 14:
                return ((jjbitVec16[i2] & l2) != 0L);
            case 15:
                return ((jjbitVec17[i2] & l2) != 0L);
            case 16:
                return ((jjbitVec18[i2] & l2) != 0L);
            case 17:
                return ((jjbitVec19[i2] & l2) != 0L);
            case 18:
                return ((jjbitVec20[i2] & l2) != 0L);
            case 19:
                return ((jjbitVec21[i2] & l2) != 0L);
            case 20:
                return ((jjbitVec0[i2] & l2) != 0L);
            case 22:
                return ((jjbitVec22[i2] & l2) != 0L);
            case 23:
                return ((jjbitVec23[i2] & l2) != 0L);
            case 24:
                return ((jjbitVec24[i2] & l2) != 0L);
            case 30:
                return ((jjbitVec25[i2] & l2) != 0L);
            case 31:
                return ((jjbitVec26[i2] & l2) != 0L);
            case 32:
                return ((jjbitVec27[i2] & l2) != 0L);
            case 33:
                return ((jjbitVec28[i2] & l2) != 0L);
            case 48:
                return ((jjbitVec29[i2] & l2) != 0L);
            case 49:
                return ((jjbitVec30[i2] & l2) != 0L);
            case 77:
                return ((jjbitVec31[i2] & l2) != 0L);
            case 159:
                return ((jjbitVec32[i2] & l2) != 0L);
            case 164:
                return ((jjbitVec33[i2] & l2) != 0L);
            case 215:
                return ((jjbitVec34[i2] & l2) != 0L);
            case 250:
                return ((jjbitVec35[i2] & l2) != 0L);
            case 251:
                return ((jjbitVec36[i2] & l2) != 0L);
            case 253:
                return ((jjbitVec37[i2] & l2) != 0L);
            case 254:
                return ((jjbitVec38[i2] & l2) != 0L);
            case 255:
                return ((jjbitVec39[i2] & l2) != 0L);
        }
        return (jjbitVec3[i1] & l1) != 0L;
    }

    private static final boolean jjCanMove_2(int hiByte, int i1, int i2, long l1, long l2) {
        switch (hiByte) {
            case 0:
                return ((jjbitVec40[i2] & l2) != 0L);
            case 2:
                return ((jjbitVec5[i2] & l2) != 0L);
            case 3:
                return ((jjbitVec41[i2] & l2) != 0L);
            case 4:
                return ((jjbitVec42[i2] & l2) != 0L);
            case 5:
                return ((jjbitVec43[i2] & l2) != 0L);
            case 6:
                return ((jjbitVec44[i2] & l2) != 0L);
            case 7:
                return ((jjbitVec45[i2] & l2) != 0L);
            case 9:
                return ((jjbitVec46[i2] & l2) != 0L);
            case 10:
                return ((jjbitVec47[i2] & l2) != 0L);
            case 11:
                return ((jjbitVec48[i2] & l2) != 0L);
            case 12:
                return ((jjbitVec49[i2] & l2) != 0L);
            case 13:
                return ((jjbitVec50[i2] & l2) != 0L);
            case 14:
                return ((jjbitVec51[i2] & l2) != 0L);
            case 15:
                return ((jjbitVec52[i2] & l2) != 0L);
            case 16:
                return ((jjbitVec53[i2] & l2) != 0L);
            case 17:
                return ((jjbitVec19[i2] & l2) != 0L);
            case 18:
                return ((jjbitVec20[i2] & l2) != 0L);
            case 19:
                return ((jjbitVec54[i2] & l2) != 0L);
            case 20:
                return ((jjbitVec0[i2] & l2) != 0L);
            case 22:
                return ((jjbitVec22[i2] & l2) != 0L);
            case 23:
                return ((jjbitVec55[i2] & l2) != 0L);
            case 24:
                return ((jjbitVec56[i2] & l2) != 0L);
            case 30:
                return ((jjbitVec25[i2] & l2) != 0L);
            case 31:
                return ((jjbitVec26[i2] & l2) != 0L);
            case 32:
                return ((jjbitVec57[i2] & l2) != 0L);
            case 33:
                return ((jjbitVec28[i2] & l2) != 0L);
            case 48:
                return ((jjbitVec58[i2] & l2) != 0L);
            case 49:
                return ((jjbitVec30[i2] & l2) != 0L);
            case 77:
                return ((jjbitVec31[i2] & l2) != 0L);
            case 159:
                return ((jjbitVec32[i2] & l2) != 0L);
            case 164:
                return ((jjbitVec33[i2] & l2) != 0L);
            case 215:
                return ((jjbitVec34[i2] & l2) != 0L);
            case 250:
                return ((jjbitVec35[i2] & l2) != 0L);
            case 251:
                return ((jjbitVec59[i2] & l2) != 0L);
            case 253:
                return ((jjbitVec37[i2] & l2) != 0L);
            case 254:
                return ((jjbitVec60[i2] & l2) != 0L);
            case 255:
                return ((jjbitVec61[i2] & l2) != 0L);
        }
        return (jjbitVec3[i1] & l1) != 0L;
    }

    public static void ReInit(JavaCharStream stream) {
        jjmatchedPos = jjnewStateCnt = 0;
        curLexState = defaultLexState;
        input_stream = stream;
        ReInitRounds();
    }

    private static final void ReInitRounds() {
        jjround = -2147483647;
        for (int i = 52; i-- > 0; )
            jjrounds[i] = Integer.MIN_VALUE;
    }

    public static void ReInit(JavaCharStream stream, int lexState) {
        ReInit(stream);
        SwitchTo(lexState);
    }

    public static void SwitchTo(int lexState) {
        if (lexState >= 4 || lexState < 0)
            throw new TokenMgrError("Error: Ignoring invalid lexical state : " + lexState + ". State unchanged.", 2);
        curLexState = lexState;
    }

    protected static Token jjFillToken() {
        Token t = Token.newToken(jjmatchedKind);
        t.kind = jjmatchedKind;
        String im = jjstrLiteralImages[jjmatchedKind];
        t.image = (im == null) ? JavaCharStream.GetImage() : im;
        t.beginLine = JavaCharStream.getBeginLine();
        t.beginColumn = JavaCharStream.getBeginColumn();
        t.endLine = JavaCharStream.getEndLine();
        t.endColumn = JavaCharStream.getEndColumn();
        return t;
    }

    public static Token getNextToken() {
        Token specialToken = null;
        int curPos = 0;
        label88:
        while (true) {
            try {
                curChar = JavaCharStream.BeginToken();
            } catch (IOException e) {
                jjmatchedKind = 0;
                Token matchedToken = jjFillToken();
                matchedToken.specialToken = specialToken;
                return matchedToken;
            }
            image = null;
            jjimageLen = 0;
            while (true) {
                switch (curLexState) {
                    case 0:
                        try {
                            JavaCharStream.backup(0);
                            while (curChar <= ' ' && (0x100003600L & 1L << curChar) != 0L)
                                curChar = JavaCharStream.BeginToken();
                        } catch (IOException e1) {
                            continue label88;
                        }
                        jjmatchedKind = Integer.MAX_VALUE;
                        jjmatchedPos = 0;
                        curPos = jjMoveStringLiteralDfa0_0();
                        break;
                    case 1:
                        jjmatchedKind = Integer.MAX_VALUE;
                        jjmatchedPos = 0;
                        curPos = jjMoveStringLiteralDfa0_1();
                        if (jjmatchedPos == 0 && jjmatchedKind > 12)
                            jjmatchedKind = 12;
                        break;
                    case 2:
                        jjmatchedKind = Integer.MAX_VALUE;
                        jjmatchedPos = 0;
                        curPos = jjMoveStringLiteralDfa0_2();
                        if (jjmatchedPos == 0 && jjmatchedKind > 12)
                            jjmatchedKind = 12;
                        break;
                    case 3:
                        jjmatchedKind = Integer.MAX_VALUE;
                        jjmatchedPos = 0;
                        curPos = jjMoveStringLiteralDfa0_3();
                        if (jjmatchedPos == 0 && jjmatchedKind > 12)
                            jjmatchedKind = 12;
                        break;
                }
                if (jjmatchedKind != Integer.MAX_VALUE) {
                    if (jjmatchedPos + 1 < curPos)
                        JavaCharStream.backup(curPos - jjmatchedPos - 1);
                    if ((jjtoToken[jjmatchedKind >> 6] & 1L << (jjmatchedKind & 0x3F)) != 0L) {
                        Token matchedToken = jjFillToken();
                        matchedToken.specialToken = specialToken;
                        TokenLexicalActions(matchedToken);
                        if (jjnewLexState[jjmatchedKind] != -1)
                            curLexState = jjnewLexState[jjmatchedKind];
                        return matchedToken;
                    }
                    if ((jjtoSkip[jjmatchedKind >> 6] & 1L << (jjmatchedKind & 0x3F)) != 0L) {
                        if ((jjtoSpecial[jjmatchedKind >> 6] & 1L << (jjmatchedKind & 0x3F)) != 0L) {
                            Token matchedToken = jjFillToken();
                            if (specialToken == null) {
                                specialToken = matchedToken;
                            } else {
                                matchedToken.specialToken = specialToken;
                                specialToken = specialToken.next = matchedToken;
                            }
                            SkipLexicalActions(matchedToken);
                        } else {
                            SkipLexicalActions(null);
                        }
                        if (jjnewLexState[jjmatchedKind] != -1) {
                            curLexState = jjnewLexState[jjmatchedKind];
                            continue label88;
                        }
                        continue label88;
                    }
                    MoreLexicalActions();
                    if (jjnewLexState[jjmatchedKind] != -1)
                        curLexState = jjnewLexState[jjmatchedKind];
                    curPos = 0;
                    jjmatchedKind = Integer.MAX_VALUE;
                    try {
                        curChar = JavaCharStream.readChar();
                        continue;
                    } catch (IOException e1) {
                        break;
                    }
                }
                break;
            }
            break;
        }
        int error_line = JavaCharStream.getEndLine();
        int error_column = JavaCharStream.getEndColumn();
        String error_after = null;
        boolean EOFSeen = false;
        try {
            JavaCharStream.readChar();
            JavaCharStream.backup(1);
        } catch (IOException e1) {
            EOFSeen = true;
            error_after = (curPos <= 1) ? "" : JavaCharStream.GetImage();
            if (curChar == '\n' || curChar == '\r') {
                error_line++;
                error_column = 0;
            } else {
                error_column++;
            }
        }
        if (!EOFSeen) {
            JavaCharStream.backup(1);
            error_after = (curPos <= 1) ? "" : JavaCharStream.GetImage();
        }
        throw new TokenMgrError(EOFSeen, curLexState, error_line, error_column, error_after, curChar, 0);
    }

    static void SkipLexicalActions(Token matchedToken) {
        switch (jjmatchedKind) {
            case 9:
                if (image == null)
                    image = new StringBuffer();
                image.append(JavaCharStream.GetSuffix(jjimageLen + (lengthOfMatch = jjmatchedPos + 1)));
                JavaCCParser.addSingleLineComment(matchedToken);
                break;
            case 10:
                if (image == null)
                    image = new StringBuffer();
                image.append(JavaCharStream.GetSuffix(jjimageLen + (lengthOfMatch = jjmatchedPos + 1)));
                JavaCCParser.addDocComment(matchedToken);
                break;
            case 11:
                if (image == null)
                    image = new StringBuffer();
                image.append(JavaCharStream.GetSuffix(jjimageLen + (lengthOfMatch = jjmatchedPos + 1)));
                JavaCCParser.addMultiLineComment(matchedToken);
                break;
        }
    }

    static void MoreLexicalActions() {
        jjimageLen += lengthOfMatch = jjmatchedPos + 1;
        switch (jjmatchedKind) {
            case 7:
                if (image == null)
                    image = new StringBuffer();
                image.append(JavaCharStream.GetSuffix(jjimageLen));
                jjimageLen = 0;
                JavaCharStream.backup(1);
                break;
        }
    }

    static void TokenLexicalActions(Token matchedToken) {
        switch (jjmatchedKind) {
            case 14:
                if (image == null)
                    image = new StringBuffer();
                image.append(jjstrLiteralImages[14]);
                if (!JavaCCParser.jdk1_4)
                    matchedToken.kind = 76;
                break;
            case 15:
                if (image == null)
                    image = new StringBuffer();
                image.append(jjstrLiteralImages[15]);
                if (!JavaCCParser.jdk1_5) ;
                break;
            case 29:
                if (image == null)
                    image = new StringBuffer();
                image.append(jjstrLiteralImages[29]);
                if (!JavaCCParser.jdk1_5)
                    matchedToken.kind = 76;
                break;
            case 122:
                if (image == null)
                    image = new StringBuffer();
                image.append(jjstrLiteralImages[122]);
                matchedToken.kind = 124;
                ((Token.GTToken) matchedToken).realKind = 122;
                JavaCharStream.backup(2);
                matchedToken.image = ">";
                break;
            case 123:
                if (image == null)
                    image = new StringBuffer();
                image.append(jjstrLiteralImages[123]);
                matchedToken.kind = 124;
                ((Token.GTToken) matchedToken).realKind = 123;
                JavaCharStream.backup(1);
                matchedToken.image = ">";
                break;
        }
    }
}
