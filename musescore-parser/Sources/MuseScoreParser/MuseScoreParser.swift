// MuseScoreParser - Pure Swift parser for MuseScore (.mscz/.mscx) files
// SPDX-License-Identifier: MIT

import Foundation
#if canImport(FoundationXML)
import FoundationXML
#endif
import ZIPFoundation

// MARK: - Data Model

/// Top-level representation of a MuseScore file
public struct MuseScoreFile: Sendable {
    public let formatVersion: String
    public let score: Score
}

public struct Score: Sendable {
    public let division: Int  // ticks per quarter note
    public let metaTags: [String: String]
    public let parts: [Part]
    public let staves: [Staff]
}

public struct Part: Sendable {
    public let id: String
    public let trackName: String
    public let instrument: Instrument
    public let staffIds: [String]
}

public struct Instrument: Sendable {
    public let id: String
    public let longName: String
    public let shortName: String
    public let trackName: String
    public let minPitch: Int?
    public let maxPitch: Int?
    public let channel: Channel?
}

public struct Channel: Sendable {
    public let program: Int
}

public struct Staff: Sendable {
    public let id: String
    public let measures: [Measure]
}

public struct Measure: Sendable {
    public let voices: [[MeasureElement]]
}

public enum MeasureElement: Sendable {
    case chord(Chord)
    case rest(Rest)
    case timeSig(TimeSig)
    case keySig(KeySig)
    case clef(Clef)
    case barline(Barline)
    case direction(Direction)
    case unknown(tag: String)
}

public struct Chord: Sendable {
    public let durationType: DurationType
    public let dots: Int
    public let notes: [Note]
    public let articulations: [String]
    public let lyrics: [Lyric]
}

public struct Rest: Sendable {
    public let durationType: DurationType
    public let dots: Int
}

public struct Note: Sendable {
    public let pitch: Int        // MIDI pitch (0-127)
    public let tpc: Int          // tonal pitch class
    public let velocity: Int?    // optional velocity override
    public let tied: Bool        // is this note tied to the next
    public let accidental: String?
}

public struct TimeSig: Sendable {
    public let numerator: Int
    public let denominator: Int
}

public struct KeySig: Sendable {
    public let accidental: Int  // negative = flats, positive = sharps
}

public struct Clef: Sendable {
    public let clefType: String  // G, F, C, etc.
}

public struct Barline: Sendable {
    public let subtype: String
}

public struct Direction: Sendable {
    public let type: String
}

public struct Lyric: Sendable {
    public let text: String
    public let syllabic: String?  // single, begin, middle, end
    public let no: Int            // verse number
}

public enum DurationType: String, Sendable {
    case whole
    case half
    case quarter
    case eighth
    case sixteenth = "16th"
    case thirtySecond = "32nd"
    case sixtyFourth = "64th"
    case hundredTwentyEighth = "128th"
    case breve
    case long
    case measure  // for whole-measure rests
    case unknown

    public init(from string: String) {
        self = DurationType(rawValue: string) ?? .unknown
    }

    /// Duration in quarter-note units (e.g. whole=4, half=2, quarter=1)
    public var quarterNoteValue: Double {
        switch self {
        case .long: return 16.0
        case .breve: return 8.0
        case .whole: return 4.0
        case .half: return 2.0
        case .quarter: return 1.0
        case .eighth: return 0.5
        case .sixteenth: return 0.25
        case .thirtySecond: return 0.125
        case .sixtyFourth: return 0.0625
        case .hundredTwentyEighth: return 0.03125
        case .measure: return 4.0  // default assumption
        case .unknown: return 1.0
        }
    }
}

// MARK: - Errors

public enum MuseScoreParserError: Error, CustomStringConvertible {
    case fileNotFound(String)
    case notAZipFile
    case noMSCXFound
    case invalidXML(String)
    case missingElement(String)
    case unsupportedVersion(String)

    public var description: String {
        switch self {
        case .fileNotFound(let path): return "File not found: \(path)"
        case .notAZipFile: return "Not a valid ZIP/.mscz file"
        case .noMSCXFound: return "No .mscx file found inside .mscz archive"
        case .invalidXML(let msg): return "Invalid XML: \(msg)"
        case .missingElement(let name): return "Missing required element: \(name)"
        case .unsupportedVersion(let v): return "Unsupported MuseScore version: \(v)"
        }
    }
}

// MARK: - Parser

public struct MuseScoreParser: Sendable {
    public init() {}

    /// Parse a .mscz (ZIP) or .mscx (XML) file from a file path
    public func parse(fileAt path: String) throws -> MuseScoreFile {
        let url = URL(fileURLWithPath: path)
        let data = try Data(contentsOf: url)

        if path.hasSuffix(".mscz") {
            return try parseMSCZ(data: data)
        } else if path.hasSuffix(".mscx") {
            return try parseMSCX(data: data)
        } else {
            // Try to detect format
            if data.count >= 2 && data[0] == 0x50 && data[1] == 0x4B {
                return try parseMSCZ(data: data)
            }
            return try parseMSCX(data: data)
        }
    }

    /// Parse a .mscz (ZIP archive) from raw data
    public func parseMSCZ(data: Data) throws -> MuseScoreFile {
        guard let archive = Archive(data: data, accessMode: .read) else {
            throw MuseScoreParserError.notAZipFile
        }

        // Find the .mscx file inside the archive
        var mscxData: Data?
        for entry in archive {
            if entry.path.hasSuffix(".mscx") {
                var entryData = Data()
                _ = try archive.extract(entry) { chunk in
                    entryData.append(chunk)
                }
                mscxData = entryData
                break
            }
        }

        guard let xmlData = mscxData else {
            throw MuseScoreParserError.noMSCXFound
        }

        return try parseMSCX(data: xmlData)
    }

    /// Parse a .mscx (XML) from raw data
    public func parseMSCX(data: Data) throws -> MuseScoreFile {
        let doc: XMLDocument
        do {
            doc = try XMLDocument(data: data, options: [])
        } catch {
            throw MuseScoreParserError.invalidXML(error.localizedDescription)
        }

        guard let root = doc.rootElement(), root.name == "museScore" else {
            throw MuseScoreParserError.invalidXML("Root element must be <museScore>")
        }

        let version = root.attribute(forName: "version")?.stringValue ?? "unknown"

        guard let scoreElement = root.elements(forName: "Score").first else {
            throw MuseScoreParserError.missingElement("Score")
        }

        let score = try parseScore(scoreElement)
        return MuseScoreFile(formatVersion: version, score: score)
    }

    // MARK: - Private parsing methods

    private func parseScore(_ elem: XMLElement) throws -> Score {
        let division = Int(elem.elements(forName: "Division").first?.stringValue ?? "480") ?? 480

        // Meta tags
        var metaTags: [String: String] = [:]
        for meta in elem.elements(forName: "metaTag") {
            if let name = meta.attribute(forName: "name")?.stringValue,
               let value = meta.stringValue {
                metaTags[name] = value
            }
        }

        // Parts
        var parts: [Part] = []
        for partElem in elem.elements(forName: "Part") {
            parts.append(try parsePart(partElem))
        }

        // Staves (top-level Staff elements contain measures)
        var staves: [Staff] = []
        for staffElem in elem.elements(forName: "Staff") {
            // Only parse staves that contain Measure elements (not the ones inside Part)
            if staffElem.elements(forName: "Measure").count > 0 {
                staves.append(try parseStaff(staffElem))
            }
        }

        return Score(
            division: division,
            metaTags: metaTags,
            parts: parts,
            staves: staves
        )
    }

    private func parsePart(_ elem: XMLElement) throws -> Part {
        let id = elem.attribute(forName: "id")?.stringValue ?? ""
        let trackName = elem.elements(forName: "trackName").first?.stringValue ?? ""

        var staffIds: [String] = []
        for staffElem in elem.elements(forName: "Staff") {
            if let sid = staffElem.attribute(forName: "id")?.stringValue {
                staffIds.append(sid)
            }
        }

        let instrument = parseInstrument(
            elem.elements(forName: "Instrument").first
        )

        return Part(id: id, trackName: trackName, instrument: instrument, staffIds: staffIds)
    }

    private func parseInstrument(_ elem: XMLElement?) -> Instrument {
        guard let elem = elem else {
            return Instrument(id: "", longName: "", shortName: "", trackName: "",
                              minPitch: nil, maxPitch: nil, channel: nil)
        }
        let id = elem.attribute(forName: "id")?.stringValue ?? ""
        let longName = elem.elements(forName: "longName").first?.stringValue ?? ""
        let shortName = elem.elements(forName: "shortName").first?.stringValue ?? ""
        let trackName = elem.elements(forName: "trackName").first?.stringValue ?? ""
        let minPitch = Int(elem.elements(forName: "minPitchP").first?.stringValue ?? "")
        let maxPitch = Int(elem.elements(forName: "maxPitchP").first?.stringValue ?? "")

        var channel: Channel?
        if let channelElem = elem.elements(forName: "Channel").first,
           let progElem = channelElem.elements(forName: "program").first,
           let val = Int(progElem.attribute(forName: "value")?.stringValue ?? "") {
            channel = Channel(program: val)
        }

        return Instrument(id: id, longName: longName, shortName: shortName,
                          trackName: trackName, minPitch: minPitch, maxPitch: maxPitch,
                          channel: channel)
    }

    private func parseStaff(_ elem: XMLElement) throws -> Staff {
        let id = elem.attribute(forName: "id")?.stringValue ?? ""
        var measures: [Measure] = []
        for measureElem in elem.elements(forName: "Measure") {
            measures.append(try parseMeasure(measureElem))
        }
        return Staff(id: id, measures: measures)
    }

    private func parseMeasure(_ elem: XMLElement) throws -> Measure {
        var voices: [[MeasureElement]] = []

        // In MuseScore format, <voice> elements contain the actual notes
        let voiceElements = elem.elements(forName: "voice")
        if voiceElements.isEmpty {
            // Some older formats might not have explicit voice tags
            voices.append(parseMeasureElements(elem))
        } else {
            for voiceElem in voiceElements {
                voices.append(parseMeasureElements(voiceElem))
            }
        }

        return Measure(voices: voices)
    }

    private func parseMeasureElements(_ container: XMLElement) -> [MeasureElement] {
        var elements: [MeasureElement] = []

        guard let children = container.children else { return elements }

        for child in children {
            guard let elem = child as? XMLElement, let name = elem.name else { continue }

            switch name {
            case "Chord":
                elements.append(.chord(parseChord(elem)))
            case "Rest":
                elements.append(.rest(parseRest(elem)))
            case "TimeSig":
                elements.append(.timeSig(parseTimeSig(elem)))
            case "KeySig":
                elements.append(.keySig(parseKeySig(elem)))
            case "Clef":
                elements.append(.clef(parseClef(elem)))
            case "BarLine":
                elements.append(.barline(Barline(
                    subtype: elem.elements(forName: "subtype").first?.stringValue ?? ""
                )))
            case "Dynamic", "Tempo", "RehearsalMark":
                elements.append(.direction(Direction(type: name)))
            default:
                elements.append(.unknown(tag: name))
            }
        }

        return elements
    }

    private func parseChord(_ elem: XMLElement) -> Chord {
        let durationStr = elem.elements(forName: "durationType").first?.stringValue ?? "quarter"
        let dots = Int(elem.elements(forName: "dots").first?.stringValue ?? "0") ?? 0

        var notes: [Note] = []
        for noteElem in elem.elements(forName: "Note") {
            notes.append(parseNote(noteElem))
        }

        var articulations: [String] = []
        for artElem in elem.elements(forName: "Articulation") {
            if let subtype = artElem.elements(forName: "subtype").first?.stringValue {
                articulations.append(subtype)
            }
        }

        var lyrics: [Lyric] = []
        for lyricElem in elem.elements(forName: "Lyrics") {
            lyrics.append(parseLyric(lyricElem))
        }

        return Chord(
            durationType: DurationType(from: durationStr),
            dots: dots,
            notes: notes,
            articulations: articulations,
            lyrics: lyrics
        )
    }

    private func parseRest(_ elem: XMLElement) -> Rest {
        let durationStr = elem.elements(forName: "durationType").first?.stringValue ?? "quarter"
        let dots = Int(elem.elements(forName: "dots").first?.stringValue ?? "0") ?? 0
        return Rest(
            durationType: DurationType(from: durationStr),
            dots: dots
        )
    }

    private func parseNote(_ elem: XMLElement) -> Note {
        let pitch = Int(elem.elements(forName: "pitch").first?.stringValue ?? "60") ?? 60
        let tpc = Int(elem.elements(forName: "tpc").first?.stringValue ?? "14") ?? 14
        let velocity = Int(elem.elements(forName: "velocity").first?.stringValue ?? "")
        let tied = elem.elements(forName: "Spanner").contains { spanner in
            spanner.attribute(forName: "type")?.stringValue == "Tie"
        }
        let accidental = elem.elements(forName: "Accidental").first?
            .elements(forName: "subtype").first?.stringValue

        return Note(
            pitch: pitch,
            tpc: tpc,
            velocity: velocity,
            tied: tied,
            accidental: accidental
        )
    }

    private func parseTimeSig(_ elem: XMLElement) -> TimeSig {
        let num = Int(elem.elements(forName: "sigN").first?.stringValue ?? "4") ?? 4
        let den = Int(elem.elements(forName: "sigD").first?.stringValue ?? "4") ?? 4
        return TimeSig(numerator: num, denominator: den)
    }

    private func parseKeySig(_ elem: XMLElement) -> KeySig {
        let acc = Int(elem.elements(forName: "accidental").first?.stringValue ?? "0") ?? 0
        return KeySig(accidental: acc)
    }

    private func parseClef(_ elem: XMLElement) -> Clef {
        let clefType = elem.elements(forName: "concertClefType").first?.stringValue
            ?? elem.elements(forName: "subtype").first?.stringValue
            ?? "G"
        return Clef(clefType: clefType)
    }

    private func parseLyric(_ elem: XMLElement) -> Lyric {
        let text = elem.elements(forName: "text").first?.stringValue ?? ""
        let syllabic = elem.elements(forName: "syllabic").first?.stringValue
        let no = Int(elem.elements(forName: "no").first?.stringValue ?? "0") ?? 0
        return Lyric(text: text, syllabic: syllabic, no: no)
    }
}

// MARK: - Convenience extensions

extension Note {
    /// Human-readable note name (e.g., "C4", "F#5")
    public var noteName: String {
        let noteNames = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]
        let octave = (pitch / 12) - 1
        let noteIndex = pitch % 12
        return "\(noteNames[noteIndex])\(octave)"
    }
}

extension Chord {
    /// Total duration in quarter-note units, accounting for dots
    public var totalDuration: Double {
        var d = durationType.quarterNoteValue
        var dotValue = d / 2.0
        for _ in 0..<dots {
            d += dotValue
            dotValue /= 2.0
        }
        return d
    }
}

extension Rest {
    /// Total duration in quarter-note units, accounting for dots
    public var totalDuration: Double {
        var d = durationType.quarterNoteValue
        var dotValue = d / 2.0
        for _ in 0..<dots {
            d += dotValue
            dotValue /= 2.0
        }
        return d
    }
}

extension Score {
    /// Get the title from meta tags
    public var title: String? {
        metaTags["movementTitle"] ?? metaTags["workTitle"]
    }

    /// Get the composer from meta tags
    public var composer: String? {
        metaTags["composer"]
    }
}
