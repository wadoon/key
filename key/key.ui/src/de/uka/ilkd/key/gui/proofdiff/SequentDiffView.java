package de.uka.ilkd.key.gui.proofdiff;

import javax.swing.*;

/**
 * Created by sarah on 1/26/17.
 */
public class SequentDiffView extends JSplitPane{


    public JEditorPane getBeforeSequentView() {
        return beforeSequentView;
    }

    public void setBeforeSequentView(JEditorPane beforeSequentView) {
        this.beforeSequentView = beforeSequentView;
    }

    public JEditorPane getAfterSequentView() {
        return afterSequentView;
    }

    public void setAfterSequentView(JEditorPane afterSequentView) {
        this.afterSequentView = afterSequentView;
    }

    private JEditorPane beforeSequentView;
    private JEditorPane afterSequentView;

    public SequentDiffView(){
        super(JSplitPane.VERTICAL_SPLIT);
        this.setOneTouchExpandable(true);
        this.setDividerLocation(50);

        beforeSequentView = new JEditorPane();
        afterSequentView = new JEditorPane();
        this.add(getBeforeSequentView());
        this.add(getAfterSequentView());

    }
}
/*
splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
                           listScrollPane, pictureScrollPane);
splitPane.setOneTouchExpandable(true);
splitPane.setDividerLocation(150);

//Provide minimum sizes for the two components in the split pane
Dimension minimumSize = new Dimension(100, 50);
listScrollPane.setMinimumSize(minimumSize);
pictureScrollPane.setMinimumSize(minimumSize);*/
