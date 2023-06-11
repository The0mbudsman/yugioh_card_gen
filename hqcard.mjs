import Jimp                         from 'jimp'
import {JSDOM}                      from 'jsdom'
import Canvas                       from 'canvas'
import {CanvasRenderingContext2D}   from 'canvas'
import sharp                        from 'sharp'
import fs                           from 'fs'
import log                          from 'log-to-file'
import path                         from 'path'
import {fileURLToPath}              from 'url'
import _                            from 'underscore'

// path to database of cropped art images
// expecting eg: ./ART/blue-eyes-white-dragon.jpg
const base_profile_path = "./ART/"

// we scrape this for the Type line since it's easier than manually assembling it
const base_type_url = "https://www.db.yugioh-card.com/yugiohdb/card_search.action?ope=2&cid="

// holds db of the above scraped types
const konami_types_path = './res/json/konami_types.json'
const konami_types_db = JSON.parse(fs.readFileSync(konami_types_path))

// holds the card database in json format because i'm a massive hack
const db_path = './res/json/card_db.json'
const db = JSON.parse(fs.readFileSync(db_path))

//output path for images
const output_path = './OUTPUT'

//what to create
const slug_names = ['mild-turkey',
    'blue-eyes-white-dragon',
    'accesscode-talker',
    'number-39-utopia',
    'evenly-matched',
    'roulette-spider',
    'endymion-the-mighty-master-of-magic'
]


export async function createSingle(card, konami_types, slug_name, scale) {
    const filename = fileURLToPath(import.meta.url);
    const __dirname = path.dirname(filename);
    const current_dir = path.resolve(__dirname) + "/"


    const type_db = konami_types
    var compbase
    var composite_images = []

    //debug for canvas boxes
    const dbg_rect = false
    register_fonts();

    // Add justified text to our canvas method
    (function(){
        const FILL = 0;        // const to indicate filltext render
        const STROKE = 1;
        const MEASURE = 2;
        var renderType = FILL; // used internal to set fill or stroke text
        
        var maxSpaceSize = 30; // Multiplier for max space size. If greater then no justificatoin applied
        var minSpaceSize = 0.7; // Multiplier for minimum space size
        var renderTextJustified = function(ctx,text,x,y,width,force){
            var words, wordsWidth, count, spaces, spaceWidth, adjSpace, renderer, i, textAlign, useSize, totalWidth;
            textAlign = ctx.textAlign; // get current align settings
            ctx.textAlign = "left";
            wordsWidth = 0;
            words = text.split(" ").map(word => {
                var w = ctx.measureText(word).width;                
                wordsWidth += w;
                return {
                    width : w,
                    word : word,
                };
            });
            // count = num words, spaces = number spaces, spaceWidth normal space size
            // adjSpace new space size >= min size. useSize Resulting space size used to render
            count = words.length;
            spaces = count - 1;
            spaceWidth = ctx.measureText(" ").width;
            adjSpace = Math.max(spaceWidth * minSpaceSize, (width - wordsWidth) / spaces);
            useSize = adjSpace > spaceWidth * maxSpaceSize ? spaceWidth : adjSpace;
            totalWidth = wordsWidth + useSize * spaces
            if(renderType === MEASURE){ // if measuring return size
                ctx.textAlign = textAlign;
                return totalWidth;
            }
            renderer = renderType === FILL ? ctx.fillText.bind(ctx) : ctx.strokeText.bind(ctx); // fill or stroke
            switch(textAlign){
                case "right":
                    x -= totalWidth;
                    break;
                case "end":
                    x += width - totalWidth;
                    break;
                case "center": // intentional fall through to default
                    x -= totalWidth / 2;                     
                default:
            }
            if (force){
                // forces all text to be on one line
                renderer(text,x,y,ctx.canvas.width);

            } else{
                if(useSize === spaceWidth){ // if space size unchanged
                    if (text.includes("● ")){
                        text = text.replace("● ", "●")
                    }
                    renderer(text,x,y);
                } else {
                    for(var i = 0; i < count; i += 1){
                        renderer(words[i].word,x,y);
                        x += words[i].width;
                        x += useSize;
                        if (words[i].word == "●" && i==0){
                            x-=useSize
                            useSize += useSize / spaces
                        }
                    }
                }
            }
            ctx.textAlign = textAlign;
        }
        // Parse vet and set settings object.
        var justifiedTextSettings = function(settings){
            var min,max;
            var vetNumber = (num, defaultNum) => {
                num = num !== null && num !== null && !isNaN(num) ? num : defaultNum;
                if(num < 0){
                    num = defaultNum;
                }
                return num;
            }
            if(settings === undefined || settings === null){
                return;
            }
            max = vetNumber(settings.maxSpaceSize, maxSpaceSize);
            min = vetNumber(settings.minSpaceSize, minSpaceSize);
            if(min > max){
                return;
            }
            minSpaceSize = min;
            maxSpaceSize = max;
        }
        // define fill text
        var fillJustifyText = function(text, x, y, width, settings, force=false){
            justifiedTextSettings(settings);
            renderType = FILL;
            renderTextJustified(this, text, x, y, width,force);
        }
        // define stroke text
        var strokeJustifyText = function(text, x, y, width, settings){
            justifiedTextSettings(settings);
            renderType = STROKE;
            renderTextJustified(this, text, x, y, width);
        }
        // define measure text
        var measureJustifiedText = function(text, width, settings){
            justifiedTextSettings(settings);
            renderType = MEASURE;
            return renderTextJustified(this, text, 0, 0, width);
        }
        // code point A
        // set the prototypes
        CanvasRenderingContext2D.prototype.fillJustifyText = fillJustifyText;
        CanvasRenderingContext2D.prototype.strokeJustifyText = strokeJustifyText;
        CanvasRenderingContext2D.prototype.measureJustifiedText = measureJustifiedText;  
    })();

    (function(){
        // code point A
        if(typeof CanvasRenderingContext2D.prototype.fillJustifyText !== "function"){
            throw new ReferenceError("Justified Paragraph extension missing requiered CanvasCanvasRenderingContext2D justified text extension");
        }
        var maxSpaceSize = 6; // Multiplier for max space size. If greater then no justificatoin applied
        var minSpaceSize = 0.5; // Multiplier for minimum space size   
        var compact = true; // if true then try and fit as many words as possible. If false then try to get the spacing as close as possible to normal
        var lineSpacing = 1.5; // space between lines
        const noJustifySetting = {  // This setting forces justified text off. Used to render last line of paragraph.
            minSpaceSize : 1,
            maxSpaceSize : 1,
        }
    
        // Parse vet and set settings object.
        var justifiedTextSettings = function(settings){
            var min, max;
            var vetNumber = (num, defaultNum) => {
                num = num !== null && num !== null && !isNaN(num) ? num : defaultNum;
                return num < 0 ? defaultNum : num;
            }
            if(settings === undefined || settings === null){ return; }
            compact = settings.compact === true ? true : settings.compact === false ? false : compact;
            max = vetNumber(settings.maxSpaceSize, maxSpaceSize);
            min = vetNumber(settings.minSpaceSize, minSpaceSize);
            lineSpacing = vetNumber(settings.lineSpacing, lineSpacing);
            if(min > max){ return; }
            minSpaceSize = min;
            maxSpaceSize = max;
        }        
        var getFontSize = function(font){  // get the font size. 
            var numFind = /[0-9]+/;
            var number = numFind.exec(font)[0];
            if(isNaN(number)){
                throw new ReferenceError("justifiedPar Cant find font size");
            }
            return Number(number);
        }
        function justifiedPar(ctx, textObj, x, y, width, settings, stroke){
            var spaceWidth, minS, maxS, words, count, lines, lineWidth, lastLineWidth, lastSize, i, renderer, fontSize, adjSpace, spaces, word, lineWords, lineFound, justifyThisLine, forceThisLine
            spaceWidth = ctx.measureText(" ").width;
            minS = spaceWidth * minSpaceSize;
            maxS = spaceWidth * maxSpaceSize;


            var text = textObj.mainText
            var material = textObj.material
            words = text.split(" ").map(word => {  // measure all words.
                var w = ctx.measureText(word).width;                
                return {
                    width : w,
                    word : word,
                };
            });
            // count = num words, spaces = number spaces, spaceWidth normal space size
            // adjSpace new space size >= min size. useSize Resulting space size used to render
            count = 0;
            lines = [];
            if (material !== ""){
                lines.push({text: material, justifyThisLine: false, forceThisLine: true}); // and the line
            }

            // create lines by shifting words from the words array until the spacing is optimal. If compact
            // true then will true and fit as many words as possible. Else it will try and get the spacing as
            // close as possible to the normal spacing
            while(words.length > 0){
                lastLineWidth = 0;
                lastSize = -1;
                lineFound = false;
                // each line must have at least one word.
                word = words.shift();
                lineWidth = word.width;
                lineWords = [word.word];
                count = 0;
                justifyThisLine = true
                forceThisLine = false

                while(lineWidth < width && words.length > 0 && !lineFound){ // Add words to line
                    word = words.shift();
                    lineWidth += word.width;
                    lineWords.push(word.word);
                    count += 1;
                    spaces = count - 1;
                    adjSpace =  (width - lineWidth) / spaces;
                    if (word.word.match(/\n/) || word.word.match(/\r\n/)){
                        if (lineWidth + (spaceWidth*spaces) < width ) {
                            justifyThisLine = false
                        }
                        lineFound = true
                        continue
                    }
                    if(minS > adjSpace - 10){  // if spacing less than min remove last word and finish line
                        lineFound = true;
                        words.unshift(word);
                        lineWords.pop();
                    }else{
                        if(!compact){ // if compact mode 
                            if(adjSpace < spaceWidth){ // if less than normal space width
                                if(lastSize === -1){
                                    lastSize = adjSpace;
                                }
                                // check if with last word on if its closer to space width
                                if(Math.abs(spaceWidth - adjSpace) < Math.abs(spaceWidth - lastSize)){
                                    lineFound = true; // yes keep it
                                }else{
                                    words.unshift(word);  // no better fit if last word removes
                                    lineWords.pop();
                                    lineFound = true;
                                }
                            }
                        }
                    }
                    lastSize = adjSpace; // remember spacing 
                }
                if (lines.length == 0 && lineWords.join(" ").match(/\+[^0-9]/gi)) {
                    //probably material
                    justifyThisLine = false
                }
                lines.push({text: lineWords.join(" "), justifyThisLine: justifyThisLine, forceThisLine: false}); // and the line
            }
            // lines have been worked out get font size, render, and render all the lines. last
            // line may need to be rendered as normal so it is outside the loop.
            fontSize = getFontSize(ctx.font);
            renderer = stroke === true ? ctx.strokeJustifyText.bind(ctx) : ctx.fillJustifyText.bind(ctx);
            for(var i = 0; i < lines.length - 1; i ++){
                renderer(lines[i].text, x, y, width, lines[i].justifyThisLine ? settings : noJustifySetting, lines[i].forceThisLine);
                y += lineSpacing * fontSize;
            }
            if(lines.length > 0){ // last line if left or start aligned for no justify
                renderer(lines[lines.length - 1].text, x, y, width, noJustifySetting, lines[i].forceThisLine);
                ctx.measureJustifiedText("", width, settings);
            }
            // return details about the paragraph.
            y += lineSpacing * fontSize;
            return {
                nextLine : y,
                fontSize : fontSize,
                lineHeight : lineSpacing * fontSize,
            };
        }
        // define fill
        var fillParagraphText = function(text, x, y, width, settings){
            justifiedTextSettings(settings);
            settings = {
                minSpaceSize : minSpaceSize,
                maxSpaceSize : maxSpaceSize,
            };
            return justifiedPar(this, text, x, y, width, settings);
        }
        // define stroke
        var strokeParagraphText = function(text, x, y, width, settings){
            justifiedTextSettings(settings);
            settings = {
                minSpaceSize : minSpaceSize,
                maxSpaceSize : maxSpaceSize,
            };
            return justifiedPar(this, text, x, y, width, settings,true);
        }
        CanvasRenderingContext2D.prototype.fillParaText = fillParagraphText;
        CanvasRenderingContext2D.prototype.strokeParaText = strokeParagraphText;
    })();

    log(`Creating ${slug_name}`, `${current_dir}logs/hqcard.log`);
    if (!(card.type.match(/spell/i) || card.type.match(/trap/i))) {
        // monster
        card.konami_type = await generateTypeLine(card) 
        compbase         = await loadCardFrame(card, true)
        composite_images = await Promise.all([
            getCardArt(card),
            getAttribute(card),
            getAttackDefLink(card),
            getName(card),
            getLevelsOrRanks(card),
            getType(card),
            getPendulumEffect(card),
            getEffect(card),
            getID(card)
        ])
    } else {
        // spell and trap
        card.konami_type = card.type
        compbase         = await loadCardFrame(card, false)
        composite_images = await Promise.all([
            getCardArt(card),
            getAttribute(card),
            getSpellTrapType(card),
            getName(card),
            getSTEffect(card),
            getID(card)
        ])
    }

    composite_images = composite_images.flat(1)
    composite_images = composite_images.filter(item => item !== undefined)
    let output = await compbase.composite(composite_images).toBuffer()
    if (scale !== 1) {
        output = await sharp(output).resize({width: (Math.round(2776*scale))}).toBuffer()
    }
    return output
    
     
    async function generateTypeLine(card){
        //Generates the '[Fiend/Pendulum/Synchro/Effect]' type string in the correct order
        //Because the database is missing info in places regarding "tuner" or "effect" we 
        //instead scrape the official konami db website page first because theyre all correct
        //if it doesnt exist on the konami db like some brand new OCG cards, then 
        //we generate it ourself
        //only once per card
        if (!(card.slug_name in type_db)){
            try {
                log(`Not looked up ${card.name} yet`, `${current_dir}logs/hqcard.log`);
                var dom = await JSDOM.fromURL(base_type_url+card.misc_info[0].konami_id), type
                const species = dom.window.document.body.querySelector("p[class='species']");
                type = Array.from(species.childNodes, (node) => node.textContent).join(", ");
                type = type.replace(/\s/g, "")
                type = type.replace(/\n/g, "")
                type = type.replace(/,/g, "")
                type = type.replace(/WingedBeast/g, "Winged Beast")
                type = type.replace(/SeaSerpent/g, "Sea Serpent")
                type_db[card.slug_name] = type
                card.konami_type = type
                log(`Card ${card.slug_name} as type ${type} from konami`, `${current_dir}logs/hqcard.log`);
                fs.writeFileSync(konami_types_path, JSON.stringify(type_db, null, 4));
            }
            catch (e) {
                log(e, `${current_dir}logs/hqcard.log`);
                type = `${card.race}/`
                if (card.type.match(/synchro/gi)){type+="Synchro/"}
                if (card.type.match(/fusion/gi)){type+="Fusion/"}
                if (card.type.match(/xyz/gi)){type+="XYZ/"}
                if (card.type.match(/ritual/gi)){type+="Ritual/"}
                if (card.type.match(/link/gi)){type+="Link/"}
                if (card.type.match(/token/gi)){type+="Token/"}
                if (card.type.match(/pendulum/gi) || card.desc.match(/\[ Pendulum Effect \]/)){type+="Pendulum/"}
                if (card.type.match(/tuner/gi)){type+="Tuner/"}
                if (card.type.match(/spirit/gi)){type+="Spirit/"}
                if (card.type.match(/toon/gi)){type+="Toon/"}
                if (card.type.match(/gemini/gi)){type+="Gemini/"}
                if (card.type.match(/union/gi)){type+="Union/"}
                if (card.type.match(/flip/gi)){type+="Flip/"}

                if (card.misc_info[0].has_effect){
                    if (card.type.match(/tuner/gi) && card.type.match(/normal/gi)){
                        type+="Normal/"
                    } else{
                        type+="Effect/"
                    }
                } else {
                    type+="Normal/"
                }
                if (type === `${card.race}/`) {type = `${card.race}/Normal/`}
                type  = type.slice(0, -1)
            }
        }
        else{
            type = type_db[card.slug_name]
        }
        type = `[${type}]`
        return type
    }

    async function loadCardFrame(card, isMonster){
        //finds the correct card background like spell green or effect monster orange 
        // or pendulum/whatever
        //does this based on the type string which is done first 
        // '[Fiend/Pendulum/Synchro/Effect]'
        // This is sanitised to become 'pendulumsynchro' for example.
        let wordsToSanitise = ["normal", "effect", "gemini", "spirit", "union", "card", "toon", "tuner", "flip", "monster", "\\/", "\\[", "\\]","Aqua","Beast-Warrior","Creator-God", "Winged-Beast","Divine-Beast","Divine Beast","Beast Warrior","Winged Beast","Beast","Cyberse","Dinosaur","Dragon","Fairy","Fiend","Fish","Insect", "Illusionist","Machine","Plant","Psychic","Pyro","Reptile","Rock","Sea-Serpent","Sea Serpent","Spellcaster","Thunder","Warrior","Winged","Wyrm","Zombie"];        
        let sanitisedType = ""

        sanitisedType = isMonster ? card.konami_type : card.type
        for (const word of wordsToSanitise){
            var regex = new RegExp(word,"gi");
            sanitisedType = sanitisedType.replace(regex, "").trim().toLowerCase()
        }

        if (isMonster && card.misc_info[0].has_effect && !card.type.match(/synchro|xyz|fusion|ritual/gi)){
            if (card.type.match(/tuner/gi) && card.type.match(/normal/gi)){
                sanitisedType+="normal"
            } else{
                sanitisedType+="effect"
            }
        } else if (isMonster && !card.type.match(/synchro|xyz|fusion|ritual/gi)) { 
            sanitisedType+="normal"
        }

        return sharp(`${current_dir}res/images/frames/${sanitisedType}Frame.png`);
    } 

    async function getCardArt(card){
        const currArray = []
        if (card.linkmarkers){ //links
            let image = sharp(`${base_profile_path}${slug_name}.jpg`)
            currArray.push({input: await image.metadata().then( (metadata) => {return image.resize(Math.round(624*3.4),Math.round(624*3.4)).toBuffer()}), left: 332, top:744, blend: "dest-over"}) 
            for (const linkarrow of card.linkmarkers){
                currArray.push({input: `${current_dir}res/images/link_arrows/${linkarrow}.png`,left: 0,top: 0})
            }
        }
        else if (card.konami_type.match(/pendulum/gi)){ //pendulums
            let image = await fadePendulum((await Jimp.read(`${base_profile_path}${slug_name}.jpg`)).scale(3.4))
            let to_add_b = await image.getBufferAsync("image/png")
            let to_add = await sharp(to_add_b).toBuffer()
            currArray.push({input: to_add, left: 176, top:728, blend: "dest-over"}) 
        }
        else{ //monsters,spells,traps,tokens
            let image = sharp(`${base_profile_path}${slug_name}.jpg`)
            currArray.push({input: await image.metadata().then( (metadata) => {return image.resize(Math.round(624*3.4)).toBuffer()}), left: 332, top:744, blend: "dest-over"})  
        }
        return currArray

        async function fadePendulum(Image){
            if (Image.bitmap.height > Image.bitmap.width){ //looking good
                var baseImage = Image.crop(0,0,Image.bitmap.width,2275)
                let alpha = 255
                for (var i = 1791; i < 2275; i+=1){
                    baseImage.scan(0,i,baseImage.bitmap.width, 1, function (x, y, idx) {
                            this.bitmap.data[idx+3] = alpha;
                    });
                    alpha = Math.max(alpha - .5, 0)
                }
                return baseImage
            } 
            else if (Image.bitmap.width > Image.bitmap.height){
                var ratio = 2421 / Image.bitmap.width;
                var baseImage = await Image.scale(ratio)
                // let alpha = 255
                // for (var i = 1791; i < 2275; i+=1){ 
                //     baseImage.scan(0,i,baseImage.bitmap.width, 1, function (x, y, idx) {
                //         this.bitmap.data[idx+3] = alpha;
                // });
                // alpha = Math.max(alpha - .5, 0)
                // }
                return baseImage
            } 
            else{
                console.log("Image is shit in some way") 
                baseImage = await Image.resize(2421, 2422)
                baseImage = await fadePendulum(baseImage)
                return baseImage 
                //image is shit in some way
            }
            
        }
    }
    
    async function getAttribute(card){
        const composite_images = []
        if ("attribute" in card){
            composite_images.push({input: `${current_dir}res/images/attributes/${card.attribute}.png`, left: 2356, top:188})
        } else {
            if (card.type.match(/spell/i)) {
                composite_images.push({input:`${current_dir}res/images/attributes/SPELL.png`, left: 2356, top:188})
            }
            else{
                composite_images.push({input:`${current_dir}res/images/attributes/TRAP.png`, left: 2356, top:188})
            }
        }
        return composite_images
    }

    async function getSpellTrapType(card){
        const composite_images = []
        const canvas = Canvas.createCanvas(1120, 156)
        const ctx = canvas.getContext('2d') 
        ctx.textBaseline = "top"
        ctx.textAlign = "right"
        ctx.font = '150px "SpellTrap"'
        let type = `[${card.type}` + (!card.race.match(/normal/gi) ? "   " : "") + `]`
        ctx.fillText(type, 1120, 0)
        composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 1384, top:504})

        if (!card.race.match(/normal/gi)){
            composite_images.push({input: `${current_dir}res/images/spell_trap_types/${card.race}.png`, left: 2316, top:520})
        }

        return composite_images
    }

    async function getAttackDefLink(card){
        const composite_images = []
        const canvas = Canvas.createCanvas(266, 118)
        const ctx = canvas.getContext('2d')
        ctx.textAlign = "right"
        ctx.textBaseline = "top"
        //attack
        if (dbg_rect){
            ctx.lineWidth = 2;
            ctx.strokeStyle="#FF0000";
            ctx.strokeRect(0, 0, canvas.width, canvas.height);
        }
        ctx.font = '150px "Attack"'
        if (card.atk == 0 && card.misc_info[0].question_atk == 1) {
            ctx.font = '100px "FirstEdition"'
            ctx.fillText("?", 266, 0)
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 1730, top:3675})
        } else{
            ctx.fillText("atk" in card ? card.atk : "", 266, 0)
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 1730, top:3675})
        }
        ctx.clearRect(0, 0, canvas.width, canvas.height);

        //link rating
        if ("linkval" in card){
            if (dbg_rect){
                ctx.lineWidth = 2;
                ctx.strokeStyle="#FF0000";
                ctx.strokeRect(0, 0, canvas.width, canvas.height);
            }
            ctx.font = '100px "LinkRating"'
            ctx.fillText("linkval" in card ? card.linkval : "", 266, 0)
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 2284, top:3700})
            ctx.clearRect(0, 0, canvas.width, canvas.height);
        } else {
        //def
            if (dbg_rect){
                ctx.lineWidth = 2;
                ctx.strokeStyle="#FF0000";
                ctx.strokeRect(0, 0, canvas.width, canvas.height);
            }
            ctx.font = '150px "Attack"'
            if (card.def == 0 && card.misc_info[0].question_def == 1) {
                ctx.font = '100px "FirstEdition"'
                ctx.fillText("?", 266, 0)
                composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 2280, top:3675})
            } else{
                ctx.fillText("def" in card ? card.def : "", 266, 0)
                composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 2280, top:3675})
            }
            ctx.clearRect(0, 0, canvas.width, canvas.height);

        }
        ctx.textAlign = "left"
        //ATK WORD
        if (dbg_rect){
            ctx.lineWidth = 2;
            ctx.strokeStyle="#FF0000";
            ctx.strokeRect(0, 0, canvas.width, canvas.height);
        }
        ctx.font = '150px "Attack"'
        ctx.fillText("ATK/", 0, 0)
        composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 1485, top:3675})
        ctx.clearRect(0, 0, canvas.width, canvas.height);

        if (!card.konami_type.match(/link/gi)){
            //DEF WORD
            if (dbg_rect){
                ctx.lineWidth = 2;
                ctx.strokeStyle="#FF0000";
                ctx.strokeRect(0, 0, canvas.width, canvas.height);
            }
            ctx.font = '150px "Attack"'
            ctx.fillText("DEF/", 0, 0)
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 2060, top:3675})
        }  
        else {
            //LINK WORD
            const canvas2 = Canvas.createCanvas(450, 118)
            const ctx2 = canvas2.getContext('2d')
            if (dbg_rect){
                ctx2.lineWidth = 2;
                ctx2.strokeStyle="#FF0000";
                ctx2.strokeRect(0, 0, canvas2.width, canvas2.height);
            }
            ctx2.textAlign = "left"
            ctx2.textBaseline = "top"
            ctx2.font = '90px "LinkRating"'
            ctx2.fillText("LINK−", 0, 0)
            composite_images.push({input: await sharp(canvas2.toBuffer()).toBuffer(), left: 2045, top:3700})
        }

        return composite_images
    }

    async function getName(card){
        //529 x 61
        const composite_images = []
        const canvas = Canvas.createCanvas(2116, 244)
        const ctx = canvas.getContext('2d')
        ctx.textBaseline = "top"
        ctx.font = '304px "CardName"'
        if (card.type.match(/xyz/gi) || card.type.match(/link/gi) || card.type.match(/spell/gi) || card.type.match(/trap/gi)){
            ctx.fillStyle = "white"
        }
        let name = card.name
        name = name.replace("\"","\u201C") // double quotes into sideways quotes as in a lot of the Therions
        name = name.replace("\"","\u201D") // double quotes into sideways quotes

        ctx.fillText(name, 0, 0, 2116)
        if (dbg_rect){
            ctx.lineWidth = 2;
            ctx.strokeStyle="#FF0000";
            ctx.strokeRect(0, 0, canvas.width, canvas.height);
        }
        composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 208, top:196})
        return composite_images
        
    }

    async function getLevelsOrRanks(card){
        const composite_images = []

        for (var i = 0; i < card.level ; i++){
            card.type.match(/xyz/gi) ? 
            composite_images.push({input: `${current_dir}res/images/rank.png`, left: card.level==13 ? 244+(i*182): 324+(i*182), top:500}) :
            composite_images.push({input: `${current_dir}res/images/level.png`, left: 2336-(i*182), top:500})
        }
        return composite_images 
    }

    async function getType(card){
        //54,765
        const composite_images = []

        const canvas = Canvas.createCanvas(2352, 120)
        const ctx = canvas.getContext('2d')
        ctx.textBaseline = "top"
        ctx.font = '105px "SpellTrap"'
        ctx.fillText(card.konami_type, 0,0)
        if (dbg_rect){
            ctx.lineWidth = 2;
            ctx.strokeStyle="#FF0000";
            ctx.strokeRect(0, 0, canvas.width, canvas.height);
        }
        composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 216, top:3032})
        return composite_images
    }

    async function getPendulumEffect(card){
        //54,765
        const composite_images = []

        if (!card.type.match(/pendulum/gi)){
            return composite_images
        }
        const canvas = Canvas.createCanvas(200, 200)
        const ctx = canvas.getContext('2d')
        ctx.textBaseline = "top"
        ctx.font = '190px "Attack"'
        ctx.fillText(card.scale,0,0)
        if (card.scale > 9){
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 232-40, top:2740})
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 2432-40, top:2740})
        } else{
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 232, top:2740})
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 2432, top:2740})
        }


        const canvas2 = Canvas.createCanvas(1920,430)
        const ctx2 = canvas2.getContext('2d')
        ctx2.textBaseline = "top"
        var fontsize = 70 //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
        ctx2.font = `${fontsize}px "CardEffects"`
        let pendulumEffect = card.desc.replace(/[-]{4,}/, "") //four or more dashes
        pendulumEffect = pendulumEffect.split(/\[ Monster Effect \]|\[ Flavor Text \]/gi)[0].trim()
        try {
            pendulumEffect = pendulumEffect.split(/\[ Pendulum Effect \]/gi)[1].trim()
        } catch {
            pendulumEffect = ""
        }
        pendulumEffect = pendulumEffect.replace(/\n/gi, " \n ")
        pendulumEffect = pendulumEffect.replace(/\r\n/gi, " \n ")
        while (ctx2.fillParaText({mainText: pendulumEffect, material: ""}, 0, 0, canvas2.width-8, {lineSpacing: 1}).nextLine  > canvas2.height){
            ctx2.clearRect(0, 0, canvas2.width, canvas2.height)
            fontsize = fontsize - .5
            ctx2.font = `${fontsize}px "CardEffects"`
        }
        if (dbg_rect){
            ctx2.lineWidth = 2;
            ctx2.strokeStyle="#FF0000";
            ctx2.strokeRect(0, 0, canvas2.width, canvas2.height);
        }
        composite_images.push({input: await sharp(canvas2.toBuffer()).toBuffer(), left: 432, top:2564})


        return composite_images
    }

    async function getEffect(card){
        const composite_images = []

        const canvas = Canvas.createCanvas(2352,525)
        const ctx = canvas.getContext('2d')
        ctx.textBaseline = "top"
        ctx.quality = 'best'
        var fontsize = 88
        ctx.font = `${fontsize}px "CardEffects"`
        let cardEffect
        if (card.type.match(/pendulum/gi)) {
            cardEffect = card.desc.replace(/[-]{4,}/, "") //four or more dashes
            try {
                cardEffect = cardEffect.split(/\[ Monster Effect \]|\[ Flavor Text \]/gi)[1].trim()
            } catch {}
        }
        else{
            cardEffect = card.desc    
        }

        if (card.konami_type.match(/normal/gi) && !card.konami_type.match(/fusion/gi)){
            ctx.font = `${fontsize}px "Vanilla"`
        }



        cardEffect = cardEffect.replace(/\n/gi, " \n ")
        cardEffect = cardEffect.replace(/\r\n/gi, " \n ")

        var cardMaterial = ""
        if (cardEffect.match(" \n ")) {
            const tokens = cardEffect.split(" \n ")
            if (tokens[0].match(/\+[^0-9]/gi)){
                cardMaterial = tokens.shift()
                cardEffect = tokens.join(" \n ")
            }

            //multiline
        } else{
            //singleline
            if (cardEffect.match(/\+[^0-9]/gi)){
                cardMaterial = cardEffect
                cardEffect = ""
            }
        }
        while (ctx.fillParaText({mainText: cardEffect, material: cardMaterial}, 0, 0, canvas.width-2, {lineSpacing: 1}).nextLine > canvas.height - 5){
            ctx.clearRect(0, 0, canvas.width, canvas.height)
            fontsize = fontsize - .25

            if (card.konami_type.match(/normal/gi)){
                ctx.font = `${fontsize}px "Vanilla"`
            } else {
                ctx.font = `${fontsize}px "CardEffects"`
            }
        }
        if (dbg_rect){
            ctx.lineWidth = 2;
            ctx.strokeStyle="#FF0000";
            ctx.strokeRect(0, 0, canvas.width, canvas.height);
        }
        composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 216, top:3156})
        return composite_images

    }

    async function getSTEffect(card){
        const composite_images = []

        const canvas = Canvas.createCanvas(2352,720)
        const ctx = canvas.getContext('2d')
        ctx.textBaseline = "top"
        var fontsize = 88
        ctx.font = `${fontsize}px "CardEffects"`
        let cardEffect = card.desc.replace(/\n/gi, " \n ")
        cardEffect = cardEffect.replace(/\r\n/gi, " \n ")
        while (ctx.fillParaText({mainText: cardEffect, material: ""}, 0, 0, canvas.width-2, {lineSpacing: 1}).nextLine > canvas.height - 30 ){
            ctx.clearRect(0, 0, canvas.width, canvas.height)
            fontsize = fontsize - .5
            ctx.font = `${fontsize}px "CardEffects"`
        }
        if (dbg_rect){
            ctx.lineWidth = 2;
            ctx.strokeStyle="#FF0000";
            ctx.strokeRect(0, 0, canvas.width, canvas.height);
        }
        composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 216, top:3064})
        return composite_images

    }

    async function getID(card){
        const composite_images = []

        var canvas = Canvas.createCanvas(640, 120)
        const ctx = canvas.getContext('2d')
        ctx.textBaseline = "top"
        ctx.font = '72px "ID"'
        if (card.type.match(/xyz/gi) && !card.type.match(/pendulum/gi)){
            ctx.fillStyle = "white"
        }
        ctx.fillText(card.card_images[0].id,0,0)

        composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 116, top:3856})
        ctx.clearRect(0, 0, canvas.width, canvas.height)
        ctx.font = '82px "ID"'

        if (card.type.match(/pendulum/gi)){
            ctx.textAlign = "left"
            ctx.textBaseline = "top"
            ctx.fillText(card.card_sets ? card.card_sets[0].set_code : " ",0,0)
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 200, top:3704})
        } 
        else if (card.type.match(/link/gi)){
            ctx.textAlign = "right"
            ctx.textBaseline = "top"
            ctx.fillText(card.card_sets ? card.card_sets[0].set_code : " ",640,0)
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 1650, top:2902})
        }
        else{
            ctx.textAlign = "right"
            ctx.textBaseline = "top"
            ctx.fillText(card.card_sets ? card.card_sets[0].set_code : " ",640,0)
            composite_images.push({input: await sharp(canvas.toBuffer()).toBuffer(), left: 1850, top:2902})
        }
        return composite_images

    }

    function register_fonts(){
        Canvas.registerFont(`${current_dir}res/fonts/card_name.ttf`, { family: 'CardName' })
        Canvas.registerFont(`${current_dir}res/fonts/attribute_type_spelltrapquickplay.ttf`, { family: 'SpellTrap' })
        Canvas.registerFont(`${current_dir}res/fonts/attack.ttf`, { family: 'Attack' })
        Canvas.registerFont(`${current_dir}res/fonts/link_rating.otf`, { family: 'LinkRating' })
        Canvas.registerFont(`${current_dir}res/fonts/1st_edition.ttf`, { family: 'FirstEdition' })
        Canvas.registerFont(`${current_dir}res/fonts/card_effects_new.ttf`, { family: 'CardEffects' })
        Canvas.registerFont(`${current_dir}res/fonts/vanilla_flavourtext.ttf`, { family: 'Vanilla' })
        Canvas.registerFont(`${current_dir}res/fonts/copyright_id.otf`, { family: 'ID' })
    }

}



for (const name of slug_names){
    console.log(`Creating ${name}...`)
    const card = db[name]
    console.log(card)
    await createSingle(card, konami_types_db, name, 1)
    .then(imagebuffer => sharp(imagebuffer).toFile(`${output_path}/${name}.webp`))    
}



// If you want to integrate with your own db, pull it out of sql or whatever, and create a json object of the following format:
// const card = {
//     id: 47558785,
//     name: 'Mild Turkey',
//     type: 'Pendulum Normal Monster',
//     frameType: 'normal_pendulum',
//     desc: '[ Pendulum Effect ]\r\n' +
//       "Once per turn: You can roll a six-sided die. Until the end of this turn, reduce this card's Pendulum Scale by that number (min. 1).\r\n" +
//       '----------------------------------------\r\n' +
//       '[ Flavor Text ]\r\n' +
//       'The taste of victory will bowl you over.',
//     atk: 1000,
//     def: 2000,
//     level: 4,
//     race: 'Winged Beast',
//     attribute: 'FIRE',
//     scale: 7,
//     card_sets: [
//       {
//         set_name: '2018 Mega-Tin Mega Pack',
//         set_code: 'MP18-EN028',
//         set_rarity: 'Common',
//         set_rarity_code: '(C)',
//         set_price: '1.07'
//       },
//       {
//         set_name: 'Maximum Crisis',
//         set_code: 'MACR-EN095',
//         set_rarity: 'Common',
//         set_rarity_code: '(C)',
//         set_price: '0.98'
//       }
//     ],
//     card_images: [
//       {
//         id: 47558785,
//         image_url: 'https://images.ygoprodeck.com/images/cards/47558785.jpg',
//         image_url_small: 'https://images.ygoprodeck.com/images/cards_small/47558785.jpg',
//         image_url_cropped: 'https://images.ygoprodeck.com/images/cards_cropped/47558785.jpg'
//       }
//     ],
//     card_prices: [
//       {
//         cardmarket_price: '0.02',
//         tcgplayer_price: '0.11',
//         ebay_price: '0.99',
//         amazon_price: '0.20',
//         coolstuffinc_price: '0.49'
//       }
//     ],
//     misc_info: [
//       {
//         views: 16204,
//         viewsweek: 34,
//         upvotes: 2,
//         downvotes: 0,
//         formats: [Array],
//         tcg_date: '2017-05-04',
//         ocg_date: '2016-02-11',
//         konami_id: 12393,
//         has_effect: 0
//       }
//     ],
//     slug_name: 'mild-turkey',
//     n_card_arts: 1,
//     konami_type: 'Winged Beast/Pendulum/Normal',
//     median_cost: 0.2,
//     extra_deck: false,
//     ban_status: 'Unlimited'
// }

// Call it as follows:
// await createSingle(card, konami_types_db, card.slug_name, 1)
// .then(imagebuffer => sharp(imagebuffer).toFile(`${output_path}/${card.slug_name}.webp`))   

