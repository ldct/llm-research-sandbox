import Testing
import Foundation
@testable import MuseScoreParser

@Suite("MuseScore Parser Tests")
struct MuseScoreParserTests {

    let parser = MuseScoreParser()

    func resourceURL(_ name: String) -> URL {
        // When using SPM test resources, they end up in the bundle
        let bundle = Bundle.module
        return bundle.url(forResource: name, withExtension: nil, subdirectory: "Resources")!
    }

    @Test("Parse .mscx XML file")
    func parseMSCX() throws {
        let url = resourceURL("sample.mscx")
        let data = try Data(contentsOf: url)
        let file = try parser.parseMSCX(data: data)

        #expect(file.formatVersion == "4.20")
        #expect(file.score.division == 480)
        #expect(file.score.title == "Sample Score")
        #expect(file.score.composer == "Composer")
    }

    @Test("Parse .mscz ZIP file")
    func parseMSCZ() throws {
        let url = resourceURL("sample.mscz")
        let data = try Data(contentsOf: url)
        let file = try parser.parseMSCZ(data: data)

        #expect(file.formatVersion == "4.20")
        #expect(file.score.title == "Sample Score")
    }

    @Test("Parts are parsed correctly")
    func parseParts() throws {
        let url = resourceURL("sample.mscx")
        let data = try Data(contentsOf: url)
        let file = try parser.parseMSCX(data: data)

        #expect(file.score.parts.count == 1)
        let part = file.score.parts[0]
        #expect(part.trackName == "Piano")
        #expect(part.instrument.id == "piano")
        #expect(part.instrument.longName == "Piano")
        #expect(part.instrument.shortName == "Pno.")
        #expect(part.instrument.minPitch == 21)
        #expect(part.instrument.maxPitch == 108)
        #expect(part.instrument.channel?.program == 0)
    }

    @Test("Measures and notes are parsed")
    func parseMeasures() throws {
        let url = resourceURL("sample.mscx")
        let data = try Data(contentsOf: url)
        let file = try parser.parseMSCX(data: data)

        #expect(file.score.staves.count == 1)
        let staff = file.score.staves[0]
        #expect(staff.measures.count == 4)

        // First measure: TimeSig + KeySig + Clef + 4 quarter notes (C D E F)
        let m1 = staff.measures[0]
        #expect(m1.voices.count == 1)
        let v1 = m1.voices[0]

        // Check time signature
        if case .timeSig(let ts) = v1[0] {
            #expect(ts.numerator == 4)
            #expect(ts.denominator == 4)
        } else {
            Issue.record("Expected timeSig")
        }

        // Check first note (C4 = pitch 60)
        let chords = v1.compactMap { elem -> Chord? in
            if case .chord(let c) = elem { return c }
            return nil
        }
        #expect(chords.count == 4)
        #expect(chords[0].notes[0].pitch == 60)
        #expect(chords[0].notes[0].noteName == "C4")
        #expect(chords[0].durationType == .quarter)
        #expect(chords[1].notes[0].pitch == 62)  // D4
        #expect(chords[2].notes[0].pitch == 64)  // E4
        #expect(chords[3].notes[0].pitch == 65)  // F4
    }

    @Test("Chord (multiple notes) parsing")
    func parseChord() throws {
        let url = resourceURL("sample.mscx")
        let data = try Data(contentsOf: url)
        let file = try parser.parseMSCX(data: data)

        // Measure 3: whole note chord C+E+G
        let m3 = file.score.staves[0].measures[2]
        let chords = m3.voices[0].compactMap { elem -> Chord? in
            if case .chord(let c) = elem { return c }
            return nil
        }
        #expect(chords.count == 1)
        #expect(chords[0].notes.count == 3)
        #expect(chords[0].durationType == .whole)
        #expect(chords[0].notes.map { $0.pitch } == [60, 64, 67])
    }

    @Test("Dotted notes and rests")
    func parseDottedAndRests() throws {
        let url = resourceURL("sample.mscx")
        let data = try Data(contentsOf: url)
        let file = try parser.parseMSCX(data: data)

        // Measure 4: eighth + eighth + quarter + quarter-rest + dotted-eighth + 16th
        let m4 = file.score.staves[0].measures[3]
        let elements = m4.voices[0].filter { elem in
            switch elem {
            case .chord, .rest: return true
            default: return false
            }
        }
        #expect(elements.count == 6)

        // Check the rest
        if case .rest(let r) = elements[3] {
            #expect(r.durationType == .quarter)
            #expect(r.totalDuration == 1.0)
        } else {
            Issue.record("Expected rest at index 3")
        }

        // Check dotted eighth
        if case .chord(let c) = elements[4] {
            #expect(c.durationType == .eighth)
            #expect(c.dots == 1)
            #expect(c.totalDuration == 0.75)  // 0.5 + 0.25
        } else {
            Issue.record("Expected dotted eighth chord at index 4")
        }

        // Check 16th
        if case .chord(let c) = elements[5] {
            #expect(c.durationType == .sixteenth)
            #expect(c.totalDuration == 0.25)
        } else {
            Issue.record("Expected 16th chord at index 5")
        }
    }

    @Test("Duration calculations")
    func durationCalc() throws {
        #expect(DurationType.whole.quarterNoteValue == 4.0)
        #expect(DurationType.half.quarterNoteValue == 2.0)
        #expect(DurationType.quarter.quarterNoteValue == 1.0)
        #expect(DurationType.eighth.quarterNoteValue == 0.5)
        #expect(DurationType.sixteenth.quarterNoteValue == 0.25)
    }

    @Test("Note names")
    func noteNames() throws {
        let c4 = Note(pitch: 60, tpc: 14, velocity: nil, tied: false, accidental: nil)
        #expect(c4.noteName == "C4")

        let a4 = Note(pitch: 69, tpc: 14, velocity: nil, tied: false, accidental: nil)
        #expect(a4.noteName == "A4")

        let fSharp5 = Note(pitch: 78, tpc: 14, velocity: nil, tied: false, accidental: nil)
        #expect(fSharp5.noteName == "F#5")
    }
}
