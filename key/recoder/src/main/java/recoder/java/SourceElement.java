package recoder.java;

import recoder.ProgramFactory;

public interface SourceElement {
    SourceElement getFirstElement();

    SourceElement getLastElement();

    Position getStartPosition();

    void setStartPosition(Position paramPosition);

    Position getEndPosition();

    void setEndPosition(Position paramPosition);

    Position getRelativePosition();

    void setRelativePosition(Position paramPosition);

    ProgramFactory getFactory();

    void accept(SourceVisitor paramSourceVisitor);

    String toSource();

    SourceElement deepClone();

    class Position {
        public static final Position UNDEFINED = new Position() {
            public void setLine(int line) {
                throw new RuntimeException("Bad idea to redefine UNDEFINED Position");
            }

            public void setColumn(int column) {
                throw new RuntimeException("Bad idea to redefine UNDEFINED Position");
            }

            public void setPosition(int line, int column) {
                throw new RuntimeException("Bad idea to redefine UNDEFINED Position");
            }
        };
        private int line;
        private int column;

        Position() {
            this.line = this.column = -1;
        }

        public Position(int line, int column) {
            setPosition(line, column);
        }

        public int getLine() {
            return this.line;
        }

        public void setLine(int line) {
            if (line < 0)
                throw new IllegalArgumentException("Negative line position " + line);
            this.line = line;
            if (this.column < 0)
                this.column = 0;
        }

        public int getColumn() {
            return this.column;
        }

        public void setColumn(int column) {
            if (column < 0)
                throw new IllegalArgumentException("Negative column position " + column);
            this.column = column;
            if (this.line < 0)
                this.line = 0;
        }

        public void setPosition(int line, int column) {
            if (line < 0)
                throw new IllegalArgumentException("Negative line position " + line);
            if (column < 0)
                throw new IllegalArgumentException("Negative column position " + column);
            this.line = line;
            this.column = column;
        }

        public int hashCode() {
            return this.column | this.line << 8;
        }

        public boolean equals(Object x) {
            if (x == this)
                return true;
            if (!(x instanceof Position))
                return false;
            Position p = (Position) x;
            return (this.line == p.line && this.column == p.column);
        }

        public int compareTo(Object x) {
            return compareTo((Position) x);
        }

        public int compareTo(Position p) {
            return (this.line == p.line) ? (this.column - p.column) : (this.line - p.line);
        }

        public String toString() {
            if (this != UNDEFINED) {
                StringBuffer buf = new StringBuffer();
                buf.append(this.line).append('/').append(this.column - 1);
                return buf.toString();
            }
            return "??/??";
        }
    }
}
