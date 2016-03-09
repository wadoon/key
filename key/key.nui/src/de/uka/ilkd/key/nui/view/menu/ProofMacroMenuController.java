package de.uka.ilkd.key.nui.view.menu;

import java.util.HashMap;
import java.util.Map;

import org.key_project.util.reflection.ClassLoaderUtil;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.ProofMacroMenu;
import de.uka.ilkd.key.gui.ProofMacroWorker;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.proof.Node;
import javafx.fxml.FXML;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;

/**
 * Copied from ProofMacroMenu and adapted to JavaFX style. This is NOT a menu
 * anymore but a view controller. There is a field rootMenu to access the actual
 * menu.
 * 
 * @see ProofMacroMenu
 * @author Victor Schuemmer
 */
public class ProofMacroMenuController extends ViewController {

    @FXML
    private Menu rootMenu;

    /**
     * The loader used to access the providers for macros.
     *
     * This is used as iteration source in other parts of KeY's ui.
     */
    public static final Iterable<ProofMacro> REGISTERED_MACROS = ClassLoaderUtil.loadServices(ProofMacro.class);
    
    public void init(KeYMediator mediator, PosInOccurrence posInOcc) {
        // Macros are grouped according to their category.
        // Store the sub menus in this map.
        Map<String, Menu> submenus = new HashMap<String, Menu>();

        Node node = mediator.getSelectedNode();
        for (ProofMacro macro : REGISTERED_MACROS) {

            boolean applicable = node != null && macro.canApplyTo(node, posInOcc);

            // NOTE (DS): At the moment, JoinRule is an experimental
            // feature. We therefore only add join-related macros
            // if the feature is currently active.
            // TODO (DS): Remove below check related to the exp. \\
            // feature once JoinRule is considered stable.
            if (!Main.isExperimentalMode() && macro.getName().contains("join")) {
                applicable = false;
            }

            if (applicable) {
                MenuItem menuItem = createMenuItem(macro, mediator, posInOcc);

                String category = macro.getCategory();
                Menu submenu = rootMenu;
                if (category != null) {
                    submenu = submenus.get(category);
                    if (submenu == null) {
                        submenu = new Menu(category);
                        submenus.put(category, submenu);
                        rootMenu.getItems().add(submenu);
                    }
                }

                submenu.getItems().add(menuItem);
            }
        }
    }

    private MenuItem createMenuItem(final ProofMacro macro, final KeYMediator mediator,
            final PosInOccurrence posInOcc) {

        MenuItem menuItem = new MenuItem(macro.getName());

        menuItem.setOnAction(e -> {
            if (mediator.isInAutoMode()) {
                return;
            }
            final ProofMacroWorker worker = new ProofMacroWorker(macro, mediator, posInOcc);
            mediator.stopInterface(true);
            mediator.setInteractive(false);
            mediator.addInterruptedListener(worker);
            worker.execute();
        });

        return menuItem;
    }


}
