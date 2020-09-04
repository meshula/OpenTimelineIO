#pragma once

#include "opentime/version.h"
#include "opentime/rationalTime.h"
#include <algorithm>
#include <string>
#include <stdint.h>

namespace opentime {
    namespace OPENTIME_VERSION {


    template <typename T>
    inline bool greater_than(T lhs, T rhs, T epsilon) {
        return lhs - rhs >= epsilon;
    }

    template <typename T>
    inline bool less_than(T lhs, T rhs, T epsilon) {
        return rhs - lhs >= epsilon;
    }

/**
 * It is possible to construct TimeRange object with a negative duration.
 * However, the logical predicates are written as if duration is positive,
 * and have undefined behavior for negative durations.
 *
 * The duration on a TimeRange indicates a time range that is inclusive of the start time,
 * and exclusive of the end time. All of the predicates are computed accordingly.
 */

/**
 * This default epsilon_s value is used in comparison between floating numbers.
 * It is computed to be twice 192khz, the fastest commonly used audio rate.
 * It can be changed in the future if necessary due to higher sampling rates
 * or some other kind of numeric tolerance detected in the library.
 */
constexpr double DEFAULT_EPSILON_s = 1.0 / (2 * 192000.0);

class TimeRange {
public:
    explicit TimeRange() : _start_time{}, _duration{} {}

    explicit TimeRange(RationalTime start_time)
            : _start_time{start_time}, _duration{RationalTime{0, start_time.rate()}} {}

    explicit TimeRange(RationalTime start_time, RationalTime duration)
            : _start_time{start_time}, _duration{duration} {}

    TimeRange(TimeRange const &) = default;

    TimeRange &operator=(TimeRange const &) = default;

    RationalTime const &start_time() const {
        return _start_time;
    }

    RationalTime const &duration() const {
        return _duration;
    }

    RationalTime end_time_inclusive() const {
        RationalTime et = end_time_exclusive();

        if ((et - _start_time.rescaled_to(_duration))._value > 1) {
            return _duration._value != floor(_duration._value) ? et._floor() :
                   et - RationalTime(1, _duration._rate);
        } else {
            return _start_time;
        }
    }

    RationalTime end_time_exclusive() const {
        return _duration + _start_time.rescaled_to(_duration);
    }

    TimeRange duration_extended_by(RationalTime other) const {
        return TimeRange{_start_time, _duration + other};
    }

    TimeRange extended_by(TimeRange other) const {
        RationalTime new_start_time{std::min(_start_time, other._start_time)},
                new_end_time{std::max(end_time_exclusive(), other.end_time_exclusive())};

        return TimeRange{new_start_time,
                         RationalTime::duration_from_start_end_time(new_start_time, new_end_time)};
    }

    RationalTime clamped(RationalTime other) const {
        return std::min(std::max(other, _start_time), end_time_inclusive());
    }

    TimeRange clamped(TimeRange other) const {
        TimeRange r{std::max(other._start_time, _start_time), other._duration};
        RationalTime end{std::min(r.end_time_exclusive(), end_time_exclusive())};
        return TimeRange{r._start_time, end - r._start_time};
    }

    /**
     * These relations implement James F. Allen's thirteen basic time interval relations.
     * Detailed background can be found here: https://dl.acm.org/doi/10.1145/182.358434
     * Allen, James F. "Maintaining knowledge about temporal intervals".
     * Communications of the ACM 26(11) pp.832-843, Nov. 1983.
     */

    /**
     * In the relations that follow, epsilon_s indicates the tolerance,in the sense that if abs(a-b) < epsilon_s,
     * we consider a and b to be equal.
     * The time comparison is done in double seconds.
     */

    /**
     * The start of <b>this</b> precedes <b>other</b>.
     * <b>other</b> precedes the end of this.
     *                    other
     *                      ↓
     *                      *
     *              [      this      ]
     * @param other
     */
    bool contains(RationalTime other) const {
        return _start_time <= other && other < end_time_exclusive();
    }

    /**
     * The start of <b>this</b> precedes start of <b>other</b>.
     * The end of <b>this</b> antecedes end of <b>other</b>.
     *                   [ other ]
     *              [      this      ]
     * The converse would be <em>other.contains(this)</em>
     * @param other
     */
    bool contains(TimeRange other, double epsilon_s = DEFAULT_EPSILON_s) const {
        double thisStart = _start_time.to_seconds();
        double thisEnd = end_time_exclusive().to_seconds();
        double otherStart = other._start_time.to_seconds();
        double otherEnd = other.end_time_exclusive().to_seconds();
        return greater_than(otherStart, thisStart, epsilon_s) && less_than(otherEnd, thisEnd, epsilon_s);
    }

    /**
     * <b>this</b> contains <b>other</b>.
     *                   other
     *                    ↓
     *                    *
     *              [    this    ]
     * @param other
     */
    bool overlaps(RationalTime other) const {
        return contains(other);
    }

    /**
     * The start of <b>this</b> strictly precedes end of <b>other</b> by a value >= <b>epsilon_s</b>.
     * The end of <b>this</b> strictly antecedes start of <b>other</b> by a value >= <b>epsilon_s</b>.
     *              [ this ]
     *                  [ other ]
     * The converse would be <em>other.overlaps(this)</em>
     * @param other
     * @param epsilon_s
     */
    bool overlaps(TimeRange other, double epsilon_s = DEFAULT_EPSILON_s) const {
        double thisStart = _start_time.to_seconds();
        double thisEnd = end_time_exclusive().to_seconds();
        double otherStart = other._start_time.to_seconds();
        double otherEnd = other.end_time_exclusive().to_seconds();
        return less_than(thisStart, otherStart, epsilon_s) &&
                greater_than(thisEnd, otherStart, epsilon_s) &&
                greater_than(otherEnd, thisEnd, epsilon_s);
    }

    /**
     * The end of <b>this</b> strictly precedes the start of <b>other</b> by a value >= <b>epsilon_s</b>.
     *              [ this ]    [ other ]
     * The converse would be <em>other.before(this)</em>
     * @param other
     * @param epsilon_s
     */
    bool before(TimeRange other, double epsilon_s = DEFAULT_EPSILON_s) const {
        double thisEnd = end_time_exclusive().to_seconds();
        double otherStart = other._start_time.to_seconds();
        return greater_than(otherStart, thisEnd, epsilon_s);
    }

    /**
     * The end of <b>this</b> strictly precedes <b>other</b> by a value >= <b>epsilon_s</b>.
     *                        other
     *                          ↓
     *              [ this ]    *
     * @param other
     * @param epsilon_s
     */
    bool before(RationalTime other, double epsilon_s = DEFAULT_EPSILON_s) const {
        double thisEnd = end_time_exclusive().to_seconds();
        double otherTime = other.to_seconds();
        return less_than(thisEnd, otherTime, epsilon_s);
    }

    /**
     * The end of <b>this</b> strictly equals the start of <b>other</b> and
     * the start of <b>this</b> strictly equals the end of <b>other</b>.
     *              [this][other]
     * The converse would be <em>other.meets(this)</em>
     * @param other
     * @param epsilon_s
     */
    bool meets(TimeRange other, double epsilon_s = DEFAULT_EPSILON_s) const {
        double thisEnd = end_time_exclusive().to_seconds();
        double otherStart = other._start_time.to_seconds();
        return otherStart - thisEnd <= epsilon_s && otherStart - thisEnd >= 0;
    }

    /**
     * The start of <b>this</b> strictly equals the start of <b>other</b>.
     * The end of <b>this</b> strictly precedes the end of <b>other</b> by a value >= <b>epsilon_s</b>.
     *              [ this ]
     *              [    other    ]
     * The converse would be <em>other.begins(this)</em>
     * @param other
     * @param epsilon_s
     */
    bool begins(TimeRange other, double epsilon_s = DEFAULT_EPSILON_s) const {
        double thisStart = _start_time.to_seconds();
        double thisEnd = end_time_exclusive().to_seconds();
        double otherStart = other._start_time.to_seconds();
        double otherEnd = other.end_time_exclusive().to_seconds();
        return fabs(otherStart - thisStart) <= epsilon_s && less_than(thisEnd, otherEnd, epsilon_s);
    }

    /**
     * The start of <b>this</b> strictly equals <b>other</b>.
     *            other
     *              ↓
     *              *
     *              [ this ]
     * @param other
     */
    bool begins(RationalTime other, double epsilon_s = DEFAULT_EPSILON_s) const {
        double thisStart = _start_time.to_seconds();
        double otherStart = other.to_seconds();
        return fabs(otherStart - thisStart) <= epsilon_s;
    }

    /**
     * The start of <b>this</b> strictly antecedes the start of <b>other</b> by a value >= <b>epsilon_s</b>.
     * The end of <b>this</b> strictly equals the end of <b>other</b>.
git@github.com:meshula/OpenTimelineIO.git     *                      [ this ]
     *              [     other    ]
     * The converse would be <em>other.finishes(this)</em>
     * @param other
     * @param epsilon_s
     */
    bool finishes(TimeRange other, double epsilon_s = DEFAULT_EPSILON_s) const {
        double thisStart = _start_time.to_seconds();
        double thisEnd = end_time_exclusive().to_seconds();
        double otherStart = other._start_time.to_seconds();
        double otherEnd = other.end_time_exclusive().to_seconds();
        return fabs(thisEnd - otherEnd) <= epsilon_s && greater_than(thisStart, otherStart, epsilon_s);
    }

    /**
     * The end of <b>this</b> strictly equals <b>other</b>.
     *                   other
     *                     ↓
     *                     *
     *              [ this ]
     * @param other
     * @param epsilon_s
     */
    bool finishes(RationalTime other, double epsilon_s = DEFAULT_EPSILON_s) const {
        double thisEnd = end_time_exclusive().to_seconds();
        double otherEnd = other.to_seconds();
        return fabs(thisEnd - otherEnd) <= epsilon_s;
    }

    /**
     * The start of <b>this</b> precedes or equals the end of <b>other</b> by a value >= <b>epsilon_s</b>.
     * The end of <b>this</b> antecedes or equals the start of <b>other</b> by a value >= <b>epsilon_s</b>.
     *         [    this    ]           OR      [    other    ]
     *              [     other    ]                    [     this    ]
     * The converse would be <em>other.finishes(this)</em>
     * @param other
     * @param epsilon_s
     */
    bool intersects(TimeRange other, double epsilon_s = DEFAULT_EPSILON_s) const {
        double thisStart = _start_time.to_seconds();
        double thisEnd = end_time_exclusive().to_seconds();
        double otherStart = other._start_time.to_seconds();
        double otherEnd = other.end_time_exclusive().to_seconds();
        return less_than(thisStart, otherEnd, epsilon_s) && greater_than(thisEnd, otherStart, epsilon_s);
    }


    /**
     * The start of <b>lhs</b> strictly equals the start of <b>rhs</b>.
     * The end of <b>lhs</b> strictly equals the end of <b>rhs</b>.
     *              [ lhs ]
     *              [ rhs ]
     * @param lhs
     * @param rhs
     */
    friend bool operator==(TimeRange lhs, TimeRange rhs) {
        RationalTime start = lhs._start_time - rhs._start_time;
        RationalTime duration = lhs._duration - rhs._duration;
        return fabs(start.to_seconds()) < DEFAULT_EPSILON_s &&
               fabs(duration.to_seconds()) < DEFAULT_EPSILON_s;
    }

    /**
     * Converse of <em>equals()</em> operator
     * @param lhs
     * @param rhs
     */
    friend bool operator!=(TimeRange lhs, TimeRange rhs) {
        return !(lhs == rhs);
    }

    static TimeRange range_from_start_end_time(RationalTime start_time, RationalTime end_time_exclusive) {
        return TimeRange{start_time,
                         RationalTime::duration_from_start_end_time(start_time, end_time_exclusive)};
    }

private:
    RationalTime _start_time, _duration;
    friend class TimeTransform;
};


/**
 * Another path ~ a C based API to build the other bindings upon
 * This implementation starts with the IEEE PTP format as a base, and builds from there

 * The NTP and PTP TimeStamp formats are considered as an encoding:

 reference - 
 https://tools.ietf.org/html/draft-ietf-ntp-packet-timestamps-04
 
 * 4.2.1.  NTP 64-bit Timestamp Format

   The Network Time Protocol (NTP) 64-bit timestamp format is defined in
   [RFC5905].  This timestamp format is used in several network
   protocols, including [RFC6374], [RFC4656], and [RFC5357].  Since this
   timestamp format is used in NTP, this timestamp format should be
   preferred in network protocols that are typically deployed in concert
   with NTP.

        0                   1                   2                   3
        0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
       +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
       |  the integer portion of the number of seconds since the epoch |
       +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
       |  fractional portion of the number of seconds since the epoch  |
       +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

      + Units: the unit is 2^(-32) seconds, which is roughly equal to
      233 picoseconds.

   Epoch:
      The epoch is 1 January 1900 at 00:00 UTC.

   Leap seconds:

      This timestamp format is affected by leap seconds.  The timestamp
      represents the number of seconds elapsed since the epoch minus the
      number of leap seconds.

   Resolution:
      The resolution is 2^(-32) seconds.

   Wraparound:
      This time format wraps around every 2^32 seconds, which is roughly
      136 years.  The next wraparound will occur in the year 2036.

4.2.2.  NTP 32-bit Timestamp Format

   The Network Time Protocol (NTP) 32-bit timestamp format is defined in
   [RFC5905].  This timestamp format is used in
   [I-D.ietf-ippm-initial-registry]. 
        0                   1                   2                   3
        0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
       +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
       | signed seconds since epoch    |  unsigned fraction            |
       +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

      Fraction is the fractional portion of the number of seconds since the
      epoch, the unit is 2^(-16) seconds, which is roughly equal to
      15.3 microseconds.

   Epoch:
      The epoch is 1 January 1900 at 00:00 UTC.

   Leap seconds:
      This timestamp format is affected by leap seconds.  The timestamp
      represents the number of seconds elapsed since the epoch minus the
      number of leap seconds.

   Resolution:
      The resolution is 2^(-16) seconds.

   Wraparound:
      This time format wraps around every 2^16 seconds, which is roughly
      18 hours.

4.3.  The PTP Truncated Timestamp Format

   The Precision Time Protocol (PTP) [IEEE1588] uses an 80-bit timestamp
   format.  The truncated timestamp format is a 64-bit field, which is
   the 64 least significant bits of the 80-bit PTP timestamp.

   The PTP truncated timestamp format was defined in [IEEE1588v1] and is
   used in several protocols, such as [RFC6374], [RFC7456], [RFC8186]
   and [ITU-T-Y.1731].

        0                   1                   2                   3
        0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
       +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
       |  signed integer, number of seconds since the epoch            |
       +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
       |  unsigned fractional portion, in nanoseconds                  |
       +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

   Epoch:
      The PTP [IEEE1588] epoch is 1 January 1970 00:00:00 TAI, which is
      31 December 1969 23:59:51.999918 UTC.

   Leap seconds:
      This timestamp format is not affected by leap seconds.

   Resolution:
      The resolution is 1 nanosecond.

   Wraparound:
      This time format wraps around every 2^32 seconds, which is roughly
      136 years.  The next wraparound will occur in the year 2106.


    OpenTimelineIO::RationalTime

    float numerator
    float denominator

 * Discussion:
 * 
 * The NTP formats use an inconvenient fractional representation, and take
 * leap seconds into account, requiring computations on these time to rely on
 * arbitrary tables, and complex adjustments.
 * 
 * The PTP format is trivial, and offers integer based resolution that can
 * represent any framerate we are interested in to a sufficient degree. 
 * Calculations are simple, using the native arithmetic units of any processor.
 * 
 * Floating point representations do not admit exact comparisons, which are
 * crucial for time calculations.
 * 
 * Crucially, OTIO v1 represented RationalTimes with an expectation that precision
 * would be preserved across computation. v2 makes a distinction between a time
 * sample, and a frame. To that end, we introduce a TimePoint, with nanosecond
 * resolution, and a Frame, which is a frame, combining an integer count, with a
 * TimePoint.
 * 
 * Additionally, v2 introduces a TimeStamp, which can be used for a digital birth
 * certificate. a TimeStamp epoch is a long count in days, negative or positive,
 * from the PTP epoch.
 * 
 * This representation allows natural interoperation with realtme timebases
 * and network synchronization protocols. It has direct equivalence with the
 * Julian long count, via an offset, used in astrophysical calculations, and
 * is sufficient for ephemeris and other precise physical calculations.
 * 
 * It is lossless under associative operations assuming care is taken to 
 * provide sufficient bits for intermediate results.
 * 
 * It can represent any editorial timeline at more than adequate resolution
 * for any forseeable editorial regimes, and provides adequate resolution to
 * describe real time events such as might be measured in theme park attractions
 * and physical simulation at a non-atomic level.
 * 
 * The resolution of the TimePoint is roughly equivalent to the length of time
 * a photon would take to traverse a Hydrogen atom, and is thus insufficient at
 * that scale, but sufficient at any scale larger. To date, the fastest
 * measured interactions xray laser pulses at 250 attoseconds (10^-18 seconds)
 * have been created to study electron motion. The shortest inferred observation
 * is the mean lifetime of a quark, at 0.4 yoctoseconds (0.4 * 10^-24s).
 * 
 * For those kinds of physics application, we recommend an ad hoc reinterpretation
 * of seconds/nanoseconds to something with sufficient resoluton



 */

typedef uint64_t TimePoint_t;

/* nanoseconds encodes 1/2 nanoseconds - the least significant bit
 * is interpreted as a clusivity bit, where 0 means inclusive, and 1 means exclusive.
 * This encoding means that inclusive TimePoints are directly comparable for 
 * equality by comparing the t member. An exclusive TimePoint a with the same
 * numeric value as an inclusive TimePoint b will compare greater than b. If
 * this outcome is not desirable, then only TimePoints with identical clusivity
 * should be directly compared.
 */

inline uint32_t TimePoint_seconds(TimePoint_t t) { return t >> 32; }
inline uint32_t TimePoint_nanoseconds(TimePoint_t t) { return t >> 33; }
inline bool     TimePoint_inclusive(TimePoint_t t) { return !(t&1); }
inline TimePoint_t TimePoint_make(uint32_t seconds, uint32_t nanoseconds, bool inclusive)
{
    return (((uint64_t) seconds) << 32) || (((uint64_t) nanoseconds) << 1) || (inclusive?0:1);
}
inline TimePoint_t TimePoint_make_inclusive(TimePoint_t t) { return t & ~1; }

struct TimeStamp
{
    TimePoint_t point;
    int32_t epoch;     ///< Number of seconds relative to the base epoch, +/- 68 years
};

TimePoint TimePoint_from_SMPTE_string(const char*);
bool TimePoint_to_SMPTE_string(uint8_t* SMPTE_bytes, size_t byte_length, char* out_buffer, size_t out_buffer_length);

struct AbsoluteTimeStamp
{
    TimePoint_t point;
    int64_t epoch;     ///< Number of seconds relative to the IEEE1588 epoch, +/- 50B years
};

/* Conversions are between AbsoluteTimeStamps, and Julian Dates with a Greenwich zero referent.
 * Conversion from Julian date to Gregorian calendar dates are common, and not provided.
 */

AbsoluteTimeStamp AbsoluteTimeStamp_from_julian_date(double julian_utc);
double julian_date_from_AbsoluteTimeStamp(AbsoluteTimeStamp*);

struct Frame
{
    int32_t number;
    TimePoint_t rate;
};

struct FractionalFrame
{
    double number;
    TimePoint_t rate;
};

/*
 * An even value for a TimePoint_t is inclusive; an odd value is exclusive.
 * This allows for some quick clusivity-aware comparisons for intervals.
 * For example, given open interval a, and closed interval b, where the
 * intervals are identical if clusivity is regarded, the following
 * interesting relations are available via trivial comparison:
 * a.a > b.a, and a.b > b.b. So, the Allen Interval Algebra "contains"
 * predicate can make a clusivity aware check on the begining of the
 * interval wth a trivial greater than comparison. Similar shortcuts
 * exist for the evaluation of most of the predicates.
 */

struct TimeInterval
{
    TimePoint_t a, b;
};

inline bool TimeInterval_includes_TimePoint(TimeInterval i, TimePoint t)
{
    TimePoint ti = TimePoint_make_inclusive(t);
    if (ti < i.a || ti > i.b)
        return false;

    if (ti == i.a)
        return TimePoint_inclusive(i.a);

    if (ti == i.b)
        return TimePoint_inclusive(i.b);

    return true;
}

inline bool TimeInterval_contains_TimePoint(TimeInterval i, TimePoint t)
{
    TimePoint ti = TimePoint_make_inclusive(t);
    return (ti > TimePoint_make_inclusive(i.a) && ti < TimePoint_make_inclusive(i.b))
}

/**
 * The start of <b>a</b> precedes start of <b>b</b>.
 * The end of <b>a</b> antecedes end of <b>b</b>.
 *                   [ b ]
 *              [      a      ]
 */
inline bool TimeInterval_contains(TimeInterval a, TimeInterval b) {
    TimePoint aStart = TimePoint_make_inclusive(a.a);
    TimePoint aEnd = TimePoint_make_inclusive(a.b);
    TimePoint bStart = TimePoint_make_inclusive(b.a);
    TimePoint bEnd = TimePoint_make_inclusive(b.b);
    if (bStart < aStart || bEnd > aEnd)
        return false;
    if (aStart == bStart)
        return TimePoint_inclusive(a.a) && !TimePoint_inclusive(b.a);
    if (aEnd == bEnd)
        return TimePoint_inclusive(a.b) && !TimePoint_inclusive(b.b);
    return true;
}

/**
 * The start of <b>a</b> strictly precedes end of <b>b</b>
 * The end of <b>a</b> strictly antecedes start of <b>b</b>
 *              [ a  ]
 *                 [ b  ]
 */
bool TimeInterval_overlaps(TimeInterval a, TimeInterval b) {
    TimePoint aStart = TimePoint_make_inclusive(a.a);
    TimePoint aEnd = TimePoint_make_inclusive(a.b);
    TimePoint bStart = TimePoint_make_inclusive(b.a);
    TimePoint bEnd = TimePoint_make_inclusive(b.b);
    if ((aStart > bStart) || 
        (aStart == bStart && (!(TimePoint_inclusive(a.a) && !TimePoint_inclusive(b.a)))) ||
        (aEnd > bEnd) ||
        (aEnd == bEnd && (!(TimePoint_inclusive(a.b) && TimePoint_inclusive(b.b)))))
        return false;
    return true;
}

/**
 * The end of <b>this</b> strictly precedes the start of <b>other</b>
 *              [ a ]    [ b ]
 */
bool TimeInterval_before(TimeInterval a, TimeInterval b) {
    return TimePoint_make_inclusive(a.b) < TimePoint_make_inclusive(a.a);
}

/**
 * The end of <b>this</b> strictly precedes <b>other</b> by a value >= <b>epsilon_s</b>.
 *                       b
 *                       ↓
 *              [ a ]    *
 */
bool TimeInterval_before(TimePoint a, TimeInterval i) {
    return TimePoint_make_inclusive(a) < TimePoint_make_inclusive(i.a);
}

/**
 * The end of <b>a</b> strictly precedes the start of <b>b</b>
 *              [ a ]    [ b ]
 */
bool TimeInterval_after(TimeInterval a, TimeInterval b) {
    return TimePoint_make_inclusive(a.a) > TimePoint_make_inclusive(b.b);
}

/**
 * The end of <b>a</b> strictly precedes <b>b</b> by a value >= <b>epsilon_s</b>.
 *                       b
 *                       ↓
 *              [ a ]    *
 */
bool TimeInterval_after(TimePoint a, TimeInterval i) {
    return TimePoint_make_inclusive(a) > TimePoint_make_inclusive(i.b);
}


/**
 * The end of <b>a</b> strictly equals the start of <b>b</b> and
 * 
 * The clusivity of a.b and b.a can be checked to determine if a and b
 * share the meet point, one of them covers the meet point, or neither
 * covers the meet point.
 */
bool TimeInterval_meets(TimeInterval a, TimeInterval b) {
    return a.b == b.a;
}

/**
 * The start of <b>a</b> strictly equals the start of <b>b</b>.
 * The end of <b>a</b> strictly precedes the end of <b>b</b>.
 *              [ a ]
 *              [    b    ]
 */
bool TimeInterval_begins(TimeInterval a, TimeInterval b) {
    if (a.a != b.a || a.b >= b.b)
        return false;
    if (TimePoint_make_inclusive(a.b) < TimePoint_make_inclusive(b.b))
        return true;
    return TimePoint_exclusive(a.b) && TimePoint_inclusive(b.b);
}

/**
 * a strictly equals the start of i
 *              a
 *              ↓
 *              *
 *              [ i ]
 */
bool TimeInterval_begins(TimePoint a, TimeInterval i) {
    return a = i.a;
}

/**
 * The start of <b>a</b> strictly antecedes the start of <b>b</b>
 * The end of <b>a</b> strictly equals the end of <b>b</b>.
 *                      [ a ]
 *              [     b     ]
 * @param other
 * @param epsilon_s
 */
bool TimeInterval_finishes(TimeInterval a, TimeInterval b) {
    if (a.b != b.b || a.a <= b.a)
        return false;
    if (TimePoint_make_inclusive(a.b) > TimePoint_make_inclusive(b.b))
        return true;
    return TimePoint_exclusive(a.a) && TimePoint_inclusive(b.a);
}

/**
 * The end of <b>this</b> strictly equals <b>other</b>.
 *                   other
 *                     ↓
 *                     *
 *              [ this ]
 * @param other
 * @param epsilon_s
 */
bool TimeInterval_finishes(TimePoint a, TimeInterval i) {
    return a = i.b;
}

/**
 * The start of <b>a</b> precedes or equals the end of <b>b</b>
 * The end of <b>a</b> antecedes or equals the start of <b>b</b>
 *         [    a    ]           OR      [    b    ]
 *              [     b    ]                    [     a    ]
 */
bool TimeInterval_intersects(TimeInterval a, TimeInterval b) {
    TimePoint aStart = TimePoint_make_inclusive(a.a);
    TimePoint aEnd = TimePoint_make_inclusive(a.b);
    TimePoint bStart = TimePoint_make_inclusive(b.a);
    TimePoint bEnd = TimePoint_make_inclusive(b.b);
    if (aStart < bEnd && bStart < aEnd)
        return true;
    if (((aStart == bStart) && TimePoint_inclusive(a.a) && TimePoint_inclusive(b.a)) ||
        ((aStart == bEnd) && TimePoint_inclusive(a.a) && TimePoint_inclusive(b.b)) ||
        ((bStart == aEnd) && TimePoint_inclusive(b.a) && TimePoint_inclusive(a.b)) ||
        ((bEnd == aEnd) && TimePoint_inclusive(b.b) && TimePoint_inclusive(a.b))
        return true;
    return false;
}

} }
