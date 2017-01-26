package de.uka.ilkd.key.speclang.jml.translation;

public enum AbstractDomain {
    GEZ("GEZ", "'int _ph', '_ph >= 0'", false), B("A", "", false), C("A", "",
            false), D("A", "", false), E("A", "", false);

    private String id;
    private String formula;
    private boolean params;

    AbstractDomain(String id, String formula, boolean params) {
        this.id = id;
        this.formula = formula;
        this.params = params;
    }

    public String getFormula() {
        return formula;
    }

    public boolean getParams() {
        return params;
    }
}
