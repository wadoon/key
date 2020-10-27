package recoder.java;

import recoder.java.declaration.ParameterDeclaration;

public interface ParameterContainer extends StatementContainer {
    int getParameterDeclarationCount();

    ParameterDeclaration getParameterDeclarationAt(int paramInt);
}
