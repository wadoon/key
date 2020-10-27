package recoder.parser;

public class Token {
    public int kind;

    public int beginLine;

    public int beginColumn;

    public int endLine;

    public int endColumn;

    public String image;

    public Token next;

    public Token specialToken;

    public static final Token newToken(int ofKind) {
        switch (ofKind) {
            default:
                return new Token();
            case 122:
            case 123:
            case 124:
                break;
        }
        return new GTToken();
    }

    public String toString() {
        return this.image;
    }

    public static class GTToken extends Token {
        int realKind = 124;
    }
}
