package lexerFactories;

import org.fife.ui.rsyntaxtextarea.Style;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.json.*;
import java.awt.*;
import java.io.InputStream;
import java.util.*;
import java.util.stream.Collectors;

public class AutomaticSyntaxScheme extends SyntaxScheme {

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(AutomaticSyntaxScheme.class);

    /**
     * The prefix used for color specifications.
     */
    private static final String COLOR = "color";
    /**
     * The prefix used for font specifications.
     */
    private static final String FONT = "font";
    private static final String CATEGORY_PREFIX = "category_";

    private static final String CONTAINED_TOKENS = "contained_tokens";

    private final Map<String, String> tokenCategories = new HashMap<>();
    private final Map<String, Color> colorMapTokens = new HashMap<>();
    private final Map<String, Font> fontMapTokens = new HashMap<>();

    private final Map<String, Color> colorMapCategories = new HashMap<>();

    private final Map<String, Font> fontMapCategories = new HashMap<>();

    private final Map<String, Set<String>> categoryTokens = new HashMap<>();


    private final Map<Integer, String> tokenKinds;

    public AutomaticSyntaxScheme(JsonObject styleObject, Map<Integer, String> tokenKinds) {
        super(false);
        this.tokenKinds = tokenKinds;
        addDefaultAttributes();
        if (styleObject != null) {
            loadAttributes(styleObject);
        }
    }

    private void addDefaultAttributes() {
        String fileName = "defaultScheme.json";

        InputStream jsonFile = ANTLRLanguageSupportFactory.class
                .getResourceAsStream(fileName);
        try {
            JsonReader jsonReader = Json.createReader(jsonFile);
            JsonObject jsonObject = jsonReader.readObject();
            loadAttributes(jsonObject);
            jsonReader.close();
        } catch (Exception e) {
            // every possible exception should be caught as loading the files
            // should not break key
            // if loading the props file does not work for any reason,
            // create a warning and continue
            LOGGER.warn(String.format("Default syntax scheme file %s could not be loaded. Reason: %s",
                    fileName, e.getMessage()));
        }
    }

    private void loadAttributes(JsonObject styleObject) {
        for (String key : styleObject.keySet()) {
            /*
            If the key starts with "category_", it should provide a JsonObject defining the style
            of all tokens belonging to that category.
            Of the key starts with "short_
            Otherwise, the key is assumed to be the name of a token and provide a JsonObject returning
            the token's style.
             */
            if (key.startsWith(CATEGORY_PREFIX)) {
                // Category style
                String categoryName = key.substring(CATEGORY_PREFIX.length());
                JsonObject categoryStyle = styleObject.getJsonObject(key);
                JsonObject color = categoryStyle.getJsonObject(COLOR);
                if (color != null) {
                    int r = color.getInt("r", 0);
                    int g = color.getInt("g", 0);
                    int b = color.getInt("b", 0);
                    colorMapCategories.put(
                            categoryName,
                            new Color(r, g, b));
                }
                JsonObject font = categoryStyle.getJsonObject(FONT);
                if (font != null) {
                    String fontName = font.getString("fontName", null);
                    int style = font.getInt("style", 0);
                    int size = font.getInt("size", 12);
                    fontMapCategories.put(categoryName, new Font(fontName, style, size));
                }
                JsonArray containedTokens = categoryStyle.getJsonArray(CONTAINED_TOKENS);
                if (containedTokens != null) {
                    Set<String> tokens = containedTokens.stream().map(t -> t.toString().substring(1,t.toString().length()-1)).collect(Collectors.toSet());
                    categoryTokens.put(categoryName, tokens);
                }
            } else {
                // Token style
                JsonObject tokenStyle = styleObject.getJsonObject(key);
                JsonObject color = tokenStyle.getJsonObject(COLOR);
                if (color != null) {
                    int r = color.getInt("r", 0);
                    int g = color.getInt("g", 0);
                    int b = color.getInt("b", 0);
                    colorMapTokens.put(
                            key,
                            new Color(r, g, b));
                }
                JsonObject font = tokenStyle.getJsonObject(FONT);
                if (font != null) {
                    String fontName = font.getString("fontName", "Arial");
                    int style = font.getInt("style", 0);
                    int size = font.getInt("size", 0);
                    fontMapTokens.put(key, new Font(fontName, style, size));
                }
                String category = tokenStyle.getString("category", null);
                if (category != null) {
                    tokenCategories.put(
                            key,
                            category
                    );
                }
            }
        }
    }

    @Override
    public Style getStyle(int index) {
        Style style = new Style();
        Color color;
        Font font;
        String tokenKindName = tokenKinds.get(index);
        if (tokenKindName == null) {
            return style;
        }
        String category = tokenCategories.get(tokenKindName);
        // If no category is defined for the token, some category might contain it:
        for (Map.Entry<String, Set<String>> categoryTokenList : categoryTokens.entrySet()) {
            if (categoryTokenList.getValue().stream().anyMatch(s -> s.equals(tokenKindName))) {
                category = categoryTokenList.getKey();
                // First matching category wins
                break;
            }
        }

        // Individual token def over category token def:
        color = colorMapTokens.get(tokenKindName);
        if (color == null) {
            color = category != null ? colorMapCategories.get(category) : null;
        }
        if (color != null) {
            style.foreground = color;
        }

        font = fontMapTokens.get(tokenKindName);
        if (font == null) {
            font = category != null ? fontMapCategories.get(category) : null;
        }
        if (font != null) {
            style.font = font;
        }

        return style;
    }

}
