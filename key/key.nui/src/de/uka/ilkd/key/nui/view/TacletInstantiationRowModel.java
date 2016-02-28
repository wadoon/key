package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.logic.op.SchemaVariable;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

public class TacletInstantiationRowModel {
    private final ObjectProperty<SchemaVariable> variable;
    private final StringProperty instantiation;
    private final IntegerProperty rowNumber;
    private boolean editable;
    
    public TacletInstantiationRowModel(SchemaVariable variable, String instantiation, int rowNumber, boolean editable) {
        this.variable = new SimpleObjectProperty<SchemaVariable>(variable);
        this.instantiation = new SimpleStringProperty(instantiation != null ? instantiation : "");
        this.rowNumber = new SimpleIntegerProperty(rowNumber);
        this.editable = editable;
    }
    public TacletInstantiationRowModel(SchemaVariable variable, String instantiation, int rowNumber) {
        this(variable, instantiation, rowNumber, false);
    }
    
    public SchemaVariable getVariable() {
        return variable.get();
    }
    
    public ObjectProperty<SchemaVariable> variableProperty() {
        return variable;
    }
    
    public void setVariable(SchemaVariable variable) {
        this.variable.set(variable);
    }
    
    public String getInstantiation() {
        return instantiation.get();
    }
    
    public StringProperty instantiationProperty() {
        return instantiation;
    }
    
    public void setInstantiation(String instantiation) {
        this.instantiation.set(instantiation != null ? instantiation : "");
    }

    public int getRowNumber() {
        return rowNumber.get();
    }
    
    public IntegerProperty rowNumberProperty() {
        return rowNumber;
    }
    
    public void setRowNumber(int rowNumber) {
        this.rowNumber.set(rowNumber);
    }
    
    public boolean isEditable() {
        return editable;
    }
    
    public void setEditable(boolean editable) {
        this.editable = editable;
    }
}
