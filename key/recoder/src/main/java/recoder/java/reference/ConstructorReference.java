package recoder.java.reference;

import recoder.java.Expression;
import recoder.java.Statement;
import recoder.list.generic.ASTList;

public interface ConstructorReference extends MemberReference, Statement {
    ASTList<Expression> getArguments();

    void setArguments(ASTList<Expression> paramASTList);
}
