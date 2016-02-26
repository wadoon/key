package de.uka.ilkd.key.nui.view;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Insets;
import java.awt.Point;
import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.UnsupportedFlavorException;
import java.awt.dnd.DnDConstants;
import java.awt.dnd.DropTarget;
import java.awt.dnd.DropTargetDragEvent;
import java.awt.dnd.DropTargetDropEvent;
import java.awt.dnd.DropTargetEvent;
import java.awt.dnd.DropTargetListener;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;

import javax.swing.BoxLayout;
import javax.swing.DefaultCellEditor;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.event.ChangeEvent;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.TableCellRenderer;

import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.gui.TacletIfSelectionDialog;
import de.uka.ilkd.key.gui.utilities.BracketMatchingTextArea;
import de.uka.ilkd.key.proof.ModelChangeListener;
import de.uka.ilkd.key.proof.ModelEvent;

public class TacletInstantiationDataTable extends JTable
        implements ModelChangeListener {

    /**
     * 
     */
    private static final long serialVersionUID = 5988602390976062610L;
    // JTextArea inputArea=new JTextArea("Nothing",3,16);
    JTextArea inputArea = new BracketMatchingTextArea("Nothing", 3, 16);
    final InputEditor iEditor = new InputEditor(inputArea);
    final InputCellRenderer iRenderer = new InputCellRenderer();

    /** the number of the model the data table belongs to */
    private int modelNr;
    /** the enclosing dialog */
    private TacletInstantiationViewController owner;
    /**
     * the TacletIfSelectionPanel that shows the different possible
     * instantiations of the if-sequent or a manual entered instantiation. The
     * value is null if and only if the taclet has no if-sequent
     */
    private TacletIfSelectionDialog ifSelectionPanel;

    public TacletInstantiationDataTable(TacletInstantiationViewController owner,
            int modelNr) {

        super(owner.getModels()[modelNr].tableModel());
        this.modelNr = modelNr;
        this.owner = owner;
        owner.getModels()[modelNr].addModelChangeListener(this);
        setUpEditor();

        // And now the Drag'n'drop stuff ...
        DropTarget aDropTarget = new DropTarget(this, new DropTargetListener() {
            public void dragEnter(DropTargetDragEvent event) {
            }

            public void dragExit(DropTargetEvent event) {
            }

            public void dragOver(DropTargetDragEvent event) {
            }

            public void drop(DropTargetDropEvent event) {
                String droppedString;

                Point dropLocation = event.getLocation();
                int row = TacletInstantiationDataTable.this
                        .rowAtPoint(dropLocation);
                int column = TacletInstantiationDataTable.this
                        .columnAtPoint(dropLocation);

                if ((row != -1) && (column == 1)) {
                    // The point lies within the table and within the
                    // instantiation
                    // column ...

                    try {
                        Transferable transferable = event.getTransferable();

                        // we accept only Strings
                        if (transferable.isDataFlavorSupported(
                                DataFlavor.stringFlavor)) {

                            event.acceptDrop(DnDConstants.ACTION_MOVE);
                            droppedString = (String) transferable
                                    .getTransferData(DataFlavor.stringFlavor);
                            // now set the new entry in the table ...

                            if (droppedString != null) {

                                TacletInstantiationDataTable.this
                                        .setValueAt(droppedString, row, column);
                                TacletInstantiationDataTable.this.repaint();
                            }
                            event.getDropTargetContext().dropComplete(true);
                        }
                        else {
                            event.rejectDrop();
                        }
                    }
                    catch (IOException exception) {
                        exception.printStackTrace();
                        event.rejectDrop();
                    }
                    catch (UnsupportedFlavorException ufException) {
                        ufException.printStackTrace();
                        event.rejectDrop();
                    }
                }
                else {
                    event.rejectDrop();
                }
            }

            public void dropActionChanged(DropTargetDragEvent dtde) {
            }
        });

        this.setDropTarget(aDropTarget);

    } // end constructor

    /** Provide sane single-click editing in table */
    public javax.swing.table.TableCellEditor getCellEditor(int row, int col) {
        return iEditor;
    }

    public TableCellRenderer getCellRenderer(int row, int col) {
        return iRenderer;
    }

    public Object getValueAt(int x, int y) {
        Object value = super.getValueAt(x, y);
        if (value == null)
            return "";
        return value;
    }

    private void setUpEditor() {
        setDefaultEditor(String.class, iEditor);

    }

    /** sets the if selection panel */
    private void setIfSelectionPanel(TacletIfSelectionDialog ifSelectionPanel) {
        this.ifSelectionPanel = ifSelectionPanel;
    }

    /**
     * returns the if selection panel
     * 
     * @return the if selection panel, null if not available
     */
    TacletIfSelectionDialog getIfSelectionPanel() {
        return ifSelectionPanel;
    }

    /**
     * returns true the model has a non empty if sequent and the
     * ifSelectionPanel has been created and set. So that the method
     * getIfSelectionPanel will not return null
     * 
     * @return true iff getIfSelectionPanel does not return null
     */
    boolean hasIfSelectionPanel() {
        return getIfSelectionPanel() != null;
    }

    public void modelChanged(ModelEvent me) {
        if (me.getSource() instanceof TacletInstantiationModel) {
            setModel(((TacletInstantiationModel) me.getSource()).tableModel());
            repaint();
        }
    }

    public int getTotalColumnWidth() {
        return getColumnModel().getTotalColumnWidth();
    }

    // public int getRowHeight(int row) {
    // if (rowHeights==null) return 48;
    // return rowHeights[row]*16;
    // }

    public void editingStopped(ChangeEvent e) {
        if (modelNr == owner.current()) {
            super.editingStopped(e);
            owner.pushAllInputToModel(modelNr);
            if (owner.checkAfterEachInput()) {
                owner.setStatus(owner.getModels()[modelNr].getStatusString());
            }
        }
    }

    class InputEditor extends DefaultCellEditor {

        /**
         * 
         */
        private static final long serialVersionUID = 1547755822847646366L;
        JPanel editPanel;
        JTextArea textarea;

        public InputEditor(JTextArea ta) {
            super(new JCheckBox()); // Unfortunately, the constructor
                                    // expects a check box, combo box,
                                    // or text field.
            textarea = ta;
            editPanel = new JPanel();
            editPanel.setLayout(new BoxLayout(editPanel, BoxLayout.X_AXIS));
            editPanel.add(new JScrollPane(textarea,
                    ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                    ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED));
            JPanel buttonPanel = new JPanel(new BorderLayout());
            Insets zeroIn = new Insets(0, 0, 0, 0);
            JButton less = new JButton("-");
            less.setMargin(zeroIn);
            JButton more = new JButton("+");
            more.setMargin(zeroIn);
            Dimension small = new Dimension(20, 9999);
            buttonPanel.setMaximumSize(small);
            buttonPanel.setPreferredSize(small);
            Dimension smallSq = new Dimension(20, 20);
            less.setMaximumSize(smallSq);
            less.setMinimumSize(smallSq);
            less.setPreferredSize(smallSq);
            more.setMaximumSize(smallSq);
            more.setMinimumSize(smallSq);
            more.setPreferredSize(smallSq);
            less.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    if (textarea.getRows() > 3) {
                        textarea.setRows(textarea.getRows() - 1);
                        setRowHeight(getSelectedRow(),
                                getRowHeight(getSelectedRow()) - 16);
                        setValueAt(textarea.getText(), getSelectedRow(),
                                getSelectedColumn());
                    }
                }
            });
            more.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    textarea.setRows(textarea.getRows() + 1);
                    setRowHeight(getSelectedRow(),
                            getRowHeight(getSelectedRow()) + 16);
                    setValueAt(textarea.getText(), getSelectedRow(),
                            getSelectedColumn());
                }
            });
            buttonPanel.add(less, BorderLayout.NORTH);
            buttonPanel.add(more, BorderLayout.SOUTH);
            editPanel.add(buttonPanel);
            editorComponent = editPanel;
            setClickCountToStart(1);
            DropTarget aDropTarget = new DropTarget(ta,
                    new DropTargetListener() {
                        public void dragEnter(DropTargetDragEvent event) {
                        }

                        public void dragExit(DropTargetEvent event) {
                        }

                        public void dragOver(DropTargetDragEvent event) {
                        }

                        public void drop(DropTargetDropEvent event) {
                            Transferable transferable = event.getTransferable();
                            if (transferable.isDataFlavorSupported(
                                    DataFlavor.stringFlavor)) {
                                event.acceptDrop(DnDConstants.ACTION_MOVE);
                                try {
                                    String droppedString = (String) transferable
                                            .getTransferData(
                                                    DataFlavor.stringFlavor);
                                    int pos = textarea
                                            .viewToModel(event.getLocation());
                                    textarea.insert(droppedString, pos);
                                    event.getDropTargetContext()
                                            .dropComplete(true);
                                }
                                catch (UnsupportedFlavorException e) {
                                    e.printStackTrace();
                                    event.rejectDrop();
                                }
                                catch (java.io.IOException e) {
                                    e.printStackTrace();
                                    event.rejectDrop();
                                }
                            }
                            else {
                                event.rejectDrop();
                            }

                        }

                        public void dropActionChanged(
                                DropTargetDragEvent dtde) {
                        }
                    });
            ta.setDropTarget(aDropTarget);
        }

        protected void fireEditingStopped() {
            super.fireEditingStopped();
        }

        public Object getCellEditorValue() {
            return textarea.getText();
        }

        public void setCaretPosition(int i) {
            textarea.setCaretPosition(i);
        }

        public void setVisible(boolean b) {
            textarea.setVisible(b);
        }

        public void validate() {
            textarea.validate();
        }

        public void requestFocus() {
            textarea.requestFocus();
        }

        public Component getTableCellEditorComponent(JTable table, Object value,
                boolean isSelected, int row, int column) {
            if (value == null)
                value = "";
            textarea.setText(value.toString());
            textarea.setRows(getRowHeight(row) / 16);
            return editorComponent;
        }

    }

    class InputCellRenderer extends DefaultTableCellRenderer {

        /**
         * 
         */
        private static final long serialVersionUID = -7270236368657110379L;
        JTextArea ta = new JTextArea("nothing");

        public Component getTableCellRendererComponent(JTable table, Object obj,
                boolean isSelected, boolean hasFocus, int row, int column) {
            if (obj == null)
                obj = "";
            ta.setRows(getRowHeight(row) / 16);
            ta.setText(obj.toString());
            if (table.isCellEditable(row, 1)) {
                // ta.setBackground(Color.yellow.brighter());
                ta.setForeground(Color.black);
            }
            else {
                ta.setBackground(Color.white);
                ta.setForeground(Color.gray);
            }
            return ta;
        }
    }
}
