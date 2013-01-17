package de.uka.ilkd.key.testgeneration.xmlparser.junitparser;

import java.util.LinkedList;
import java.util.List;

public class MethodDeclaration {

    private String name;

    private List<String> parameterNames = new LinkedList<String>();

    /**
     * @return the name
     */
    public String getName() {

        return name;
    }

    /**
     * @param name
     *            the name to set
     */
    public void setName(String name) {

        this.name = name;
    }

    /**
     * @return the parameterNames
     */
    public List<String> getParameterNames() {

        return parameterNames;
    }

    /**
     * @param parameterNames
     *            the parameterNames to set
     */
    public void setParameterNames(List<String> parameterNames) {

        this.parameterNames = parameterNames;
    }

}
