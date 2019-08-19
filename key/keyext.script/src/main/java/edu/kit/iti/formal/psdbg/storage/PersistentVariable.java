package edu.kit.iti.formal.psdbg.storage;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@AllArgsConstructor
@NoArgsConstructor
public class PersistentVariable {
    private String name, type, value;
}