package de.uka.ilkd.key.nui.util;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import javafx.scene.control.TreeItem;

/**
 * reads the XML File defining the CSS Highlighting Classes and Descriptions
 * 
 * @author Maximilian Li
 * @version 1.0
 */
public class XmlReader {
    private File inputFile;
    private List<String> selectorList = new ArrayList<>();
    private Map<String, String> descriptionMap = new HashMap<>();
    private TreeItem<String> treeRoot = new TreeItem<>("root");
    private Map<String, String> classMap = new HashMap<>();
    private Map<String, Boolean> classEnabledMap = new HashMap<>();

    /**
     * Constructor for the XMLReader
     * 
     * @param path
     *            the filepath for the xml file
     * @param ruleList
     *            the list of rules as read by the {@link CssFileHandler}
     */
    public XmlReader(String path, List<CssRule> ruleList) {
        inputFile = new File(path);
        for (CssRule rule : ruleList) {
            selectorList.addAll(rule.getSelectors());
        }
        parseFile();
    }

    /**
     * parses the XML File
     */
    private void parseFile() {
        try {
            // Make Reader
            DocumentBuilderFactory dbFactory = DocumentBuilderFactory
                    .newInstance();
            DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
            Document doc = dBuilder.parse(inputFile);
            doc.getDocumentElement().normalize();
            NodeList nList = doc.getElementsByTagName("TreeItem");

            // Make new TreeItem for CSSStylerView
            for (int i = 0; i < nList.getLength(); i++) {
                Node node = nList.item(i);
                TreeItem<String> categoryNode = new TreeItem<String>(
                        ((Element) node).getAttribute("text"));
                NodeList childList = node.getChildNodes();

                // Build Maps for each Rule by Selector
                for (int j = 0; j < childList.getLength(); j++) {
                    Node child = childList.item(j);
                    if (child.getNodeType() == Node.ELEMENT_NODE) {
                        Element elem = (Element) child;
                        String selector = elem.getElementsByTagName("selector")
                                .item(0).getTextContent();
                        if (selectorList.contains(selector)) {
                            selectorList.remove(selector);

                            String description = elem
                                    .getElementsByTagName("Description").item(0)
                                    .getTextContent();

                            descriptionMap.put(selector, description);

                            String className = elem
                                    .getElementsByTagName("Class").item(0)
                                    .getTextContent();

                            classMap.put(className, selector.substring(1));

                            classEnabledMap.put(className,
                                    elem.getElementsByTagName("enabled").item(0)
                                            .getTextContent().equals("true"));

                            TreeItem<String> childNode = new TreeItem<String>(
                                    description);
                            categoryNode.getChildren().add(childNode);

                        }
                    }

                }
                treeRoot.getChildren().add(categoryNode);
            }

        }
        catch (RuntimeException e) {
            throw e;
        }
        catch (Exception e) {
            e.printStackTrace();
        }
        TreeItem<String> otherNode = new TreeItem<String>("Other");
        for (int i = 0; i < selectorList.size(); i++) {
            otherNode.getChildren()
                    .add(new TreeItem<String>(selectorList.get(i)));
        }
        treeRoot.getChildren().add(otherNode);
    }

    public TreeItem<String> getTree() {
        return treeRoot;
    }

    public Map<String, String> getDescriptionMap() {
        return descriptionMap;
    }

    public Map<String, String> getClassMap() {
        return classMap;
    }

    public Map<String, Boolean> getClassEnabledMap() {
        return classEnabledMap;
    }
}
