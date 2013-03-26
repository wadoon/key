package se.gu.svanefalk.testgeneration.core.codecoverage.executionpath;

import java.util.HashMap;

public class PathStatementNode extends PathNode {

    HashMap<String, PathNode> ast = new HashMap<String, PathNode>();
    PathStatementNode nd = null;

    public PathStatementNode() {
        this.ast.put("as", this.nd);
    }
}
