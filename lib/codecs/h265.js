/**
 * mux.js
 *
 * Copyright (c) Brightcove
 * Licensed Apache-2.0 https://github.com/videojs/mux.js/blob/master/LICENSE
 */
'use strict';

var Stream = require('../utils/stream.js');
var ExpGolomb = require('../utils/exp-golomb.js');

var H265Stream, NalByteStream;

/**
 * Accepts a NAL unit byte stream and unpacks the embedded NAL units.
 */
NalByteStream = function () {
  var
    syncPoint = 0,
    i,
    buffer;
  NalByteStream.prototype.init.call(this);

  /*
   * Scans a byte stream and triggers a data event with the NAL units found.
   * @param {Object} data Event received from H265Stream
   * @param {Uint8Array} data.data The h264 byte stream to be scanned
   *
   * @see H265Stream.push
   */
  this.push = function (data) {
    var swapBuffer;

    if (!buffer) {
      buffer = data.data;
    } else {
      swapBuffer = new Uint8Array(buffer.byteLength + data.data.byteLength);
      swapBuffer.set(buffer);
      swapBuffer.set(data.data, buffer.byteLength);
      buffer = swapBuffer;
    }
    var len = buffer.byteLength;

    // Rec. ITU-T H.264, Annex B
    // scan for NAL unit boundaries

    // a match looks like this:
    // 0 0 1 .. NAL .. 0 0 1
    // ^ sync point        ^ i
    // or this:
    // 0 0 1 .. NAL .. 0 0 0
    // ^ sync point        ^ i

    // advance the sync point to a NAL start, if necessary
    for (; syncPoint < len - 3; syncPoint++) {
      if (buffer[syncPoint + 2] === 1) {
        // the sync point is properly aligned
        i = syncPoint + 5;
        break;
      }
    }

    while (i < len) {
      // look at the current byte to determine if we've hit the end of
      // a NAL unit boundary
      switch (buffer[i]) {
        case 0:
          // skip past non-sync sequences
          if (buffer[i - 1] !== 0) {
            i += 2;
            break;
          } else if (buffer[i - 2] !== 0) {
            i++;
            break;
          }

          // deliver the NAL unit if it isn't empty
          if (syncPoint + 3 !== i - 2) {
            this.trigger('data', buffer.subarray(syncPoint + 3, i - 2));
          }

          // drop trailing zeroes
          do {
            i++;
          } while (buffer[i] !== 1 && i < len);
          syncPoint = i - 2;
          i += 3;
          break;
        case 1:
          // skip past non-sync sequences
          if (buffer[i - 1] !== 0 ||
            buffer[i - 2] !== 0) {
            i += 3;
            break;
          }

          // deliver the NAL unit
          this.trigger('data', buffer.subarray(syncPoint + 3, i - 2));
          syncPoint = i - 2;
          i += 3;
          break;
        default:
          // the current byte isn't a one or zero, so it cannot be part
          // of a sync sequence
          i += 3;
          break;
      }
    }
    // filter out the NAL units that were delivered
    buffer = buffer.subarray(syncPoint);
    i -= syncPoint;
    syncPoint = 0;
  };

  this.reset = function () {
    buffer = null;
    syncPoint = 0;
    this.trigger('reset');
  };

  this.flush = function () {
    // deliver the last buffered NAL unit
    if (buffer && buffer.byteLength > 3) {
      this.trigger('data', buffer.subarray(syncPoint + 3));
    }
    // reset the stream state
    buffer = null;
    syncPoint = 0;
    this.trigger('done');
  };

  this.endTimeline = function () {
    this.flush();
    this.trigger('endedtimeline');
  };
};
NalByteStream.prototype = new Stream();

/**
 * Accepts input from a ElementaryStream and produces H.264 NAL unit data
 * events.
 */
H265Stream = function () {
  var
    nalByteStream = new NalByteStream(),
    self,
    trackId,
    currentPts,
    currentDts,
    currentSPS,
    currentPPS,

    discardEmulationPreventionBytes,
    readSequenceParameterSet,
    skipScalingList,
    skipSubLayerHrdParameters,
    skipHrdParameter,
    skipStRefPicSet;

  H265Stream.prototype.init.call(this);
  self = this;

  /*
   * Pushes a packet from a stream onto the NalByteStream
   *
   * @param {Object} packet - A packet received from a stream
   * @param {Uint8Array} packet.data - The raw bytes of the packet
   * @param {Number} packet.dts - Decode timestamp of the packet
   * @param {Number} packet.pts - Presentation timestamp of the packet
   * @param {Number} packet.trackId - The id of the h264 track this packet came from
   * @param {('video'|'audio')} packet.type - The type of packet
   *
   */
  this.push = function (packet) {
    if (packet.type !== 'video') {
      return;
    }
    trackId = packet.trackId;
    currentPts = packet.pts;
    currentDts = packet.dts;

    nalByteStream.push(packet);
  };

  /*
   * Identify NAL unit types and pass on the NALU, trackId, presentation and decode timestamps
   * for the NALUs to the next stream component.
   * Also, preprocess caption and sequence parameter NALUs.
   *
   * @param {Uint8Array} data - A NAL unit identified by `NalByteStream.push`
   * @see NalByteStream.push
   */

  nalByteStream.on('data', function (data) {
    var
      event = {
        trackId: trackId,
        pts: currentPts,
        dts: currentDts,
        data: data
      };

    switch ((data[0] & 0x7f) >> 1) {
      case 0x20:
        event.nalUnitType = 'VPS_NUT';
        event.escapedRBSP = discardEmulationPreventionBytes(data.subarray(2));
        break;
      case 0x13:
        event.nalUnitType = 'IDR_W_RADL';
        break;
      case 0x14:
        event.nalUnitType = 'IDR_N_LP';
        break;
      case 0x27:
        event.nalUnitType = 'PREFIX_SEI_NUT';
        event.escapedRBSP = discardEmulationPreventionBytes(data.subarray(2));
        break;
      case 0x28:
        event.nalUnitType = 'SUFFIX_SEI_NUT';
        event.escapedRBSP = discardEmulationPreventionBytes(data.subarray(2));
        break;
      case 0x21:
        event.nalUnitType = 'SPS_NUT';
        event.escapedRBSP = discardEmulationPreventionBytes(data.subarray(2));
        currentSPS = event.escapedRBSP;
        if (currentPPS && currentSPS) {
          event.config = readSequenceParameterSet(currentSPS, currentPPS);
        }
        break;
      case 0x22:
        event.nalUnitType = 'PPS_NUT';
        event.escapedRBSP = discardEmulationPreventionBytes(data.subarray(2));
        currentPPS = event.escapedRBSP;
        if (currentPPS && currentSPS) {
          event.config = readSequenceParameterSet(currentSPS, currentPPS);
        }
        break;
      case 0x23:
        event.nalUnitType = 'AUD_NUT';
        break;

      default:
        break;
    }
    // This triggers data on the H265Stream
    self.trigger('data', event);
  });
  nalByteStream.on('done', function () {
    self.trigger('done');
  });
  nalByteStream.on('partialdone', function () {
    self.trigger('partialdone');
  });
  nalByteStream.on('reset', function () {
    self.trigger('reset');
  });
  nalByteStream.on('endedtimeline', function () {
    self.trigger('endedtimeline');
  });

  this.flush = function () {
    nalByteStream.flush();
  };

  this.partialFlush = function () {
    nalByteStream.partialFlush();
  };

  this.reset = function () {
    nalByteStream.reset();
  };

  this.endTimeline = function () {
    nalByteStream.endTimeline();
  };

  /**
   * Advance the ExpGolomb decoder past a scaling list. The scaling
   * list is optionally transmitted as part of a sequence parameter
   * set and is not relevant to transmuxing.
   * @param count {number} the number of entries in this scaling list
   * @param expGolombDecoder {object} an ExpGolomb pointed to the
   * start of a scaling list
   * @see Recommendation ITU-T H.265, Section 7.3.4
   */
  skipScalingList = function (expGolombDecoder) {
    for (var sizeId = 0; sizeId < 4; sizeId++) {
      for (var matrixId = 0; matrixId < 6; matrixId += (sizeId == 3) ? 3 : 1) {
        var scalingListPredModeFlag = expGolombDecoder.readBits(1);
        if (!scalingListPredModeFlag) {
          expGolombDecoder.readUnsignedExpGolomb();
        }
        else {
          var nextCoef = 8
          var coefNum = Math.min(64, (1 << (4 + (sizeId << 1))))

          if (sizeId > 1) {
            scalingListDcCoefMinus8 = expGolombDecoder.readExpGolomb();
            nextCoef = scalingListDcCoefMinus8;
          }
          for (i = 0; i < coefNum; i++) {
            expGolombDecoder.readExpGolomb(); // scaling_list_delta_coef
          }
        }
      }
    }
  };

  skipSubLayerHrdParameters = function (CpbCnt, sub_pic_hrd_params_present_flag, expGolombDecoder) {
    let i = 0;
    for (i = 0; i < CpbCnt; i++) {
      expGolombDecoder.skipUnsignedExpGolomb();
      expGolombDecoder.skipUnsignedExpGolomb();
      if (sub_pic_hrd_params_present_flag) {
        expGolombDecoder.skipUnsignedExpGolomb();
        expGolombDecoder.skipUnsignedExpGolomb();
      }
      expGolombDecoder.skipBits(1);
    }
  };

  skipHrdParameter = function (commonInfPresentFlag, maxNumSubLayersMinus1, expGolombDecoder) {
    let i = 0;
    let sub_pic_hrd_params_present_flag = 0;
    let nal_hrd_parameters_present_flag = false;
    let vcl_hrd_parameters_present_flag = false;
    if (commonInfPresentFlag) {
      nal_hrd_parameters_present_flag = expGolombDecoder.readBits(1);
      vcl_hrd_parameters_present_flag = expGolombDecoder.readBits(1);
      if (nal_hrd_parameters_present_flag || vcl_hrd_parameters_present_flag) {
        sub_pic_hrd_params_present_flag = expGolombDecoder.readBits(1);
        if (sub_pic_hrd_params_present_flag) {
          expGolombDecoder.skipBits(8);
          expGolombDecoder.skipBits(5);
          expGolombDecoder.skipBits(1);
          expGolombDecoder.skipBits(5);
        }
        expGolombDecoder.skipBits(4);
        expGolombDecoder.skipBits(4);

        if (sub_pic_hrd_params_present_flag) {
          expGolombDecoder.skipBits(4);
        }
        expGolombDecoder.skipBits(5);
        expGolombDecoder.skipBits(5);
        expGolombDecoder.skipBits(5);
      }
    }
    for (i = 0; i <= maxNumSubLayersMinus1; i++) {
      const fixed_pic_rate_general_flag = expGolombDecoder.readBits(1);
      let fixed_pic_rate_within_cvs_flag = 0;
      let low_delay_hrd_flag = 0;
      let cpbCntMinus1 = 0;
      if (!fixed_pic_rate_general_flag) {
        fixed_pic_rate_within_cvs_flag = expGolombDecoder.readBits(1);
      }
      if (fixed_pic_rate_within_cvs_flag) {
        expGolombDecoder.skipUnsignedExpGolomb();
      }
      else {
        low_delay_hrd_flag = expGolombDecoder.readBits(1);
      }
      if (!low_delay_hrd_flag) {
        cpbCntMinus1 = expGolombDecoder.readUnsignedExpGolomb();
      }
      if (nal_hrd_parameters_present_flag) {
        skipSubLayerHrdParameters(cpbCntMinus1, sub_pic_hrd_params_present_flag, expGolombDecoder);
      }
      if (vcl_hrd_parameters_present_flag) {
        skipSubLayerHrdParameters(cpbCntMinus1, sub_pic_hrd_params_present_flag, expGolombDecoder);
      }
    }
  };

  const NumNegativePics = [];
  const NumPositivePics = [];
  const DeltaPocS0 = [];
  const DeltaPocS1 = [];
  const UsedByCurrPicS0 = [];
  const UsedByCurrPicS1 = [];
  const use_delta_flag = [];
  const used_by_curr_pic_flag = [];

  skipStRefPicSet = function (stRpsIdx, num_short_term_ref_pic_sets, expGolombDecoder) {
    let inter_ref_pic_set_prediction_flag = 0;
    if (stRpsIdx != 0) {
      inter_ref_pic_set_prediction_flag = expGolombDecoder.readBits(1);
    }
    if (inter_ref_pic_set_prediction_flag) {
      let delta_idx_minus1 = 0;
      if (stRpsIdx == num_short_term_ref_pic_sets) {
        delta_idx_minus1 = expGolombDecoder.readUnsignedExpGolomb();
      }
      const delta_rps_sign = expGolombDecoder.readBits(1);
      const abs_delta_rps_minus1 = expGolombDecoder.readUnsignedExpGolomb();
      const RefRpsIdx = stRpsIdx - (delta_idx_minus1 + 1);
      const deltaRps = (1 - 2 * delta_rps_sign) * (abs_delta_rps_minus1 + 1)

      let i = 0;
      let j = 0;

      for (j = NumPositivePics[RefRpsIdx] - 1; j >= 0; j--) {
        const dPoc = DeltaPocS1[RefRpsIdx][j] + deltaRps;
        const flg = use_delta_flag[NumNegativePics[RefRpsIdx] + j] === undefined ? true : use_delta_flag[NumNegativePics[RefRpsIdx] + j];
        if (dPoc < 0 && flg) {
          DeltaPocS0[stRpsIdx][i] = dPoc
          UsedByCurrPicS0[stRpsIdx][i++] = used_by_curr_pic_flag[NumNegativePics[RefRpsIdx] + j]
        }
      }
      {
        const flg = use_delta_flag[NumDeltaPocs[RefRpsIdx]] === undefined ? true : use_delta_flag[NumDeltaPocs[RefRpsIdx]];
        if (deltaRps < 0 && flg) {
          DeltaPocS0[stRpsIdx][i] = deltaRps
          UsedByCurrPicS0[stRpsIdx][i++] = used_by_curr_pic_flag[NumDeltaPocs[RefRpsIdx]]
        }
      }
      for (j = 0; j < NumNegativePics[RefRpsIdx]; j++) {
        const dPoc = DeltaPocS0[RefRpsIdx][j] + deltaRps
        const flg = use_delta_flag[j] === undefined ? true : use_delta_flag[j];
        if (dPoc < 0 && flg) {
          DeltaPocS0[stRpsIdx][i] = dPoc
          UsedByCurrPicS0[stRpsIdx][i++] = used_by_curr_pic_flag[j]
        }
      }
      NumNegativePics[stRpsIdx] = i
      i = 0
      for (j = NumNegativePics[RefRpsIdx] - 1; j >= 0; j--) {
        const dPoc = DeltaPocS0[RefRpsIdx][j] + deltaRps
        const flg = use_delta_flag[j] === undefined ? true : use_delta_flag[j];
        if (dPoc > 0 && flg) {
          DeltaPocS1[stRpsIdx][i] = dPoc
          UsedByCurrPicS1[stRpsIdx][i++] = used_by_curr_pic_flag[j]
        }
      }
      {
        const flg = use_delta_flag[NumDeltaPocs[RefRpsIdx]] === undefined ? true : use_delta_flag[NumDeltaPocs[RefRpsIdx]];
        if (deltaRps > 0 && flg) {
          DeltaPocS1[stRpsIdx][i] = deltaRps
          UsedByCurrPicS1[stRpsIdx][i++] = used_by_curr_pic_flag[NumDeltaPocs[RefRpsIdx]]
        }
      }
      for (j = 0; j < NumPositivePics[RefRpsIdx]; j++) {
        const dPoc = DeltaPocS1[RefRpsIdx][j] + deltaRps
        const flg = use_delta_flag[NumNegativePics[RefRpsIdx] + j] === undefined ? true : use_delta_flag[NumNegativePics[RefRpsIdx] + j];
        if (dPoc > 0 && flg) {
          DeltaPocS1[stRpsIdx][i] = dPoc
          UsedByCurrPicS1[stRpsIdx][i++] = used_by_curr_pic_flag[NumNegativePics[RefRpsIdx] + j]
        }
      }
      NumPositivePics[stRpsIdx] = i

      const NumDeltaPocs = NumNegativePics[stRpsIdx] + NumPositivePics[stRpsIdx];
      for (j = 0; j <= NumDeltaPocs; j++) {
        used_by_curr_pic_flag[j] = expGolombDecoder.readBits(1);
        if (!used_by_curr_pic_flag) {
          use_delta_flag[j] = expGolombDecoder.readBits(1);
        }
      }
    } else {
      let i = 0;
      const num_negative_pics = expGolombDecoder.readUnsignedExpGolomb();
      const num_positive_pics = expGolombDecoder.readUnsignedExpGolomb();
      NumNegativePics[stRpsIdx] = num_negative_pics;
      NumPositivePics[stRpsIdx] = num_positive_pics;
      for (i = 0; i < num_negative_pics; i++) {
        const delta_poc_s0_minus1 = expGolombDecoder.readUnsignedExpGolomb();
        const used_by_curr_pic_s0_flag = expGolombDecoder.readBits(1);
        if (!UsedByCurrPicS0[stRpsIdx]) {
          UsedByCurrPicS0[stRpsIdx] = []
        }
        if (!UsedByCurrPicS0[stRpsIdx][i]) {
          UsedByCurrPicS0[stRpsIdx] = []
        }
        UsedByCurrPicS0[stRpsIdx][i] = used_by_curr_pic_s0_flag
        if (!DeltaPocS0[stRpsIdx]) {
          DeltaPocS0[stRpsIdx] = []
        }
        if (!DeltaPocS0[stRpsIdx][i]) {
          DeltaPocS0[stRpsIdx][i] = []
        }
        if (i == 0) {
          DeltaPocS0[stRpsIdx][i] = -(delta_poc_s0_minus1 + 1)
        }
        else {
          DeltaPocS0[stRpsIdx][i] = DeltaPocS0[stRpsIdx][i - 1] - (delta_poc_s0_minus1 + 1)
        }
      }
      for (i = 0; i < num_positive_pics; i++) {
        const delta_poc_s1_minus1 = expGolombDecoder.readUnsignedExpGolomb();
        const used_by_curr_pic_s1_flag = expGolombDecoder.readBits(1);
        if (!DeltaPocS1[stRpsIdx]) {
          DeltaPocS1[stRpsIdx] = []
        }
        if (!DeltaPocS1[stRpsIdx][i]) {
          DeltaPocS1[stRpsIdx][i] = []
        }
        UsedByCurrPicS1[stRpsIdx][i] = used_by_curr_pic_s1_flag
        if (i == 0) {
          DeltaPocS1[stRpsIdx][i] = delta_poc_s1_minus1 + 1
        }
        else {
          DeltaPocS1[stRpsIdx][i] = DeltaPocS1[stRpsIdx][i - 1] + (delta_poc_s1_minus1 + 1)
        }
      }
    }
  };

  /**
   * Expunge any "Emulation Prevention" bytes from a "Raw Byte
   * Sequence Payload"
   * @param data {Uint8Array} the bytes of a RBSP from a NAL
   * unit
   * @return {Uint8Array} the RBSP without any Emulation
   * Prevention Bytes
   */
  discardEmulationPreventionBytes = function (data) {
    var
      length = data.byteLength,
      emulationPreventionBytesPositions = [],
      i = 1,
      newLength, newData;

    // Find all `Emulation Prevention Bytes`
    while (i < length - 2) {
      if (data[i] === 0 && data[i + 1] === 0 && data[i + 2] === 0x03) {
        emulationPreventionBytesPositions.push(i + 2);
        i += 2;
      } else {
        i++;
      }
    }

    // If no Emulation Prevention Bytes were found just return the original
    // array
    if (emulationPreventionBytesPositions.length === 0) {
      return data;
    }

    // Create a new array to hold the NAL unit data
    newLength = length - emulationPreventionBytesPositions.length;
    newData = new Uint8Array(newLength);
    var sourceIndex = 0;

    for (i = 0; i < newLength; sourceIndex++, i++) {
      if (sourceIndex === emulationPreventionBytesPositions[0]) {
        // Skip this byte
        sourceIndex++;
        // Remove this position index
        emulationPreventionBytesPositions.shift();
      }
      newData[i] = data[sourceIndex];
    }

    return newData;
  };

  /**
   * Read a sequence parameter set and return some interesting video
   * properties. A sequence parameter set is the H264 metadata that
   * describes the properties of upcoming video frames.
   * @param data {Uint8Array} the bytes of a sequence parameter set
   * @return {object} an object with configuration parsed from the
   * sequence parameter set, including the dimensions of the
   * associated video frames.
   */
  readSequenceParameterSet = function (spsData, ppsData) {
    var
      expGolombDecoder,
      generalProfileSpace,
      generalTierFlag,
      generalProfileIdc,
      generalProfileCompatibilityFlags,
      generalConstraintIndicatorFlags,
      generalLevelIdc,
      minSpatialSegmentationIdc,
      parallelismType,
      bitDepthLumaMinus8,
      bitDepthChromaMinus8,
      avgFrameRate,
      constantFrameRate,
      numTemporalLayers,
      temporalIdNested,
      lengthSizeMinusOne,
      chromaFormatIdc,
      i;

    expGolombDecoder = new ExpGolomb(spsData);
    expGolombDecoder.skipBits(4); // sps_video_parameter_set_id
    const sps_max_sub_layers_minus1 = expGolombDecoder.readBits(3);
    const sps_temporal_id_nesting_flag = expGolombDecoder.readBits(1);

    generalProfileSpace = expGolombDecoder.readBits(2);
    generalTierFlag = expGolombDecoder.readBits(1);
    generalProfileIdc = expGolombDecoder.readBits(5);
    generalProfileCompatibilityFlags = expGolombDecoder.readBits(32);
    generalConstraintIndicatorFlags = expGolombDecoder.readBits(48);
    generalLevelIdc = expGolombDecoder.readBits(8);
    const sub_layer_profile_present_flag = [];
    const sub_layer_level_present_flag = [];
    const maxNumSubLayersMinus1 = sps_max_sub_layers_minus1;
    for (i = 0; i < maxNumSubLayersMinus1; i++) {
      sub_layer_profile_present_flag[i] = expGolombDecoder.readBits(1);
      sub_layer_level_present_flag[i] = expGolombDecoder.readBits(1);
    }
    if (maxNumSubLayersMinus1 > 0) {
      for (i = maxNumSubLayersMinus1; i < 8; i++) {
        expGolombDecoder.skipBits(2); // reserved_zero_2bits
      }
    }
    for (i = 0; i < maxNumSubLayersMinus1; i++) {
      if (sub_layer_profile_present_flag[i]) {
        expGolombDecoder.skipBits(8 + 32 + 48);
      }
      if (sub_layer_level_present_flag[1]) {
        expGolombDecoder.skipBits(8);
      }
    }
    expGolombDecoder.skipUnsignedExpGolomb(); // sps_seq_parameter_set_id
    chromaFormatIdc = expGolombDecoder.readUnsignedExpGolomb();
    if (chromaFormatIdc === 3) {
      expGolombDecoder.skipBits(1); // separate_colour_plane_flag
    }
    expGolombDecoder.skipUnsignedExpGolomb(); // pic_width_in_luma_samples
    expGolombDecoder.skipUnsignedExpGolomb(); // pic_height_in_luma_samples
    const conformance_window_flag = expGolombDecoder.readBits(1);
    let conf_win_left_offset = 0;
    let conf_win_right_offset = 0;
    let conf_win_top_offset = 0;
    let conf_win_bottom_offset = 0;
    if (conformance_window_flag) {
      conf_win_left_offset = expGolombDecoder.readUnsignedExpGolomb();
      conf_win_right_offset = expGolombDecoder.readUnsignedExpGolomb();
      conf_win_top_offset = expGolombDecoder.readUnsignedExpGolomb();
      conf_win_bottom_offset = expGolombDecoder.readUnsignedExpGolomb();
    }

    bitDepthLumaMinus8 = expGolombDecoder.readUnsignedExpGolomb();
    bitDepthChromaMinus8 = expGolombDecoder.readUnsignedExpGolomb();
    const log2_max_pic_order_cnt_lsb_minus4 = expGolombDecoder.readUnsignedExpGolomb();
    const sps_sub_layer_ordering_info_present_flag = expGolombDecoder.readBits(1);

    for (i = (sps_sub_layer_ordering_info_present_flag ? 0 : sps_max_sub_layers_minus1); i <= sps_max_sub_layers_minus1; i++) {
      expGolombDecoder.skipUnsignedExpGolomb(); // sps_max_dec_pic_buffering_minus1
      expGolombDecoder.skipUnsignedExpGolomb(); // sps_max_num_reorder_pics
      expGolombDecoder.skipUnsignedExpGolomb(); // sps_max_latency_increase_plus1
    }
    expGolombDecoder.skipUnsignedExpGolomb(); // log2_min_luma_coding_block_size_minus3
    expGolombDecoder.skipUnsignedExpGolomb(); // log2_diff_max_min_luma_coding_block_size
    expGolombDecoder.skipUnsignedExpGolomb(); // log2_min_luma_transform_block_size_minus2
    expGolombDecoder.skipUnsignedExpGolomb(); // log2_diff_max_min_luma_transform_block_size
    expGolombDecoder.skipUnsignedExpGolomb(); // max_transform_hierarchy_depth_inter
    expGolombDecoder.skipUnsignedExpGolomb(); // max_transform_hierarchy_depth_intra
    const scaling_list_enabled_flag = expGolombDecoder.readBits(1);
    if (scaling_list_enabled_flag) {
      const sps_scaling_list_data_present_flag = expGolombDecoder.readBits(1);
      if (sps_scaling_list_data_present_flag) {
        skipScalingList(expGolombDecoder);
      }
    }
    expGolombDecoder.skipBits(2); // amp_enabled_flag sample_adaptive_offset_enabled_flag
    const pcm_enabled_flag = expGolombDecoder.readBits(1);
    if (pcm_enabled_flag) {
      expGolombDecoder.skipBits(4); // pcm_sample_bit_depth_luma_minus1
      expGolombDecoder.skipBits(4); // pcm_sample_bit_depth_chroma_minus1
      expGolombDecoder.skipUnsignedExpGolomb(); // log2_min_pcm_luma_coding_block_size_minus3
      expGolombDecoder.skipUnsignedExpGolomb(); // log2_diff_max_min_pcm_luma_coding_block_size
      expGolombDecoder.skipBits(1); // pcm_loop_filter_disabled_flag
    }
    const num_short_term_ref_pic_sets = expGolombDecoder.readUnsignedExpGolomb();
    for (i = 0; i < num_short_term_ref_pic_sets; i++) {
      skipStRefPicSet(i, num_short_term_ref_pic_sets, expGolombDecoder)
    }
    const long_term_ref_pics_present_flag = expGolombDecoder.readBits(1);
    if (long_term_ref_pics_present_flag) {
      const num_long_term_ref_pics_sps = expGolombDecoder.readUnsignedExpGolomb();
      for (i = 0; i < num_long_term_ref_pics_sps; i++) {
        expGolombDecoder.skipBits(log2_max_pic_order_cnt_lsb_minus4 + 4); // lt_ref_pic_poc_lsb_sps
        expGolombDecoder.skipBits(1); // used_by_curr_pic_lt_sps_flag
      }
    }
    expGolombDecoder.skipBits(2); // sps_temporal_mvp_enabled_flag strong_intra_smoothing_enabled_flag
    const vui_parameters_present_flag = expGolombDecoder.readBits(1);
    let vui_timing_info_present_flag = false;
    let vui_num_units_in_tick = 0;
    let vui_time_scale = 0;
    if (vui_parameters_present_flag) {
      const aspect_ratio_info_present_flag = expGolombDecoder.readBits(1);
      if (aspect_ratio_info_present_flag) {
        const aspect_ratio_idc = expGolombDecoder.readBits(8);
        if (aspect_ratio_idc === 255 /*EXTENDED_SAR*/) {
          expGolombDecoder.skipBits(16);
          expGolombDecoder.skipBits(16);
        }
      }
      const overscan_info_present_flag = expGolombDecoder.readBits(1);
      if (overscan_info_present_flag) {
        expGolombDecoder.skipBits(1);
      }
      const video_signal_type_present_flag = expGolombDecoder.readBits(1);
      if (video_signal_type_present_flag) {
        expGolombDecoder.skipBits(4);
        const colour_description_present_flag = expGolombDecoder.readBits(1);
        if (colour_description_present_flag) {
          expGolombDecoder.skipBits(24);
        }
      }
      const chroma_loc_info_present_flag = expGolombDecoder.readBits(1);
      if (chroma_loc_info_present_flag) {
        expGolombDecoder.skipUnsignedExpGolomb();
        expGolombDecoder.skipUnsignedExpGolomb();
      }
      expGolombDecoder.skipBits(3);
      const default_display_window_flag = expGolombDecoder.readBits(1);
      if (default_display_window_flag) {
        expGolombDecoder.skipUnsignedExpGolomb();
        expGolombDecoder.skipUnsignedExpGolomb();
        expGolombDecoder.skipUnsignedExpGolomb();
        expGolombDecoder.skipUnsignedExpGolomb();
      }
      vui_timing_info_present_flag = expGolombDecoder.readBits(1);
      if (vui_timing_info_present_flag) {
        vui_num_units_in_tick = expGolombDecoder.readBits(32);
        vui_time_scale = expGolombDecoder.readBits(32);
        const vui_poc_proportional_to_timing_flag = expGolombDecoder.readBits(1);
        if (vui_poc_proportional_to_timing_flag) {
          expGolombDecoder.skipUnsignedExpGolomb();
        }
        const vui_hrd_parameters_present_flag = expGolombDecoder.readBits(1);
        if (vui_hrd_parameters_present_flag) {
          skipHrdParameter(1, sps_max_sub_layers_minus1, expGolombDecoder);
        }
      }
      const bitstream_restriction_flag = expGolombDecoder.readBits(1);
      if (bitstream_restriction_flag) {
        expGolombDecoder.skipBits(3);
        minSpatialSegmentationIdc = expGolombDecoder.readUnsignedExpGolomb();
      }
    }

    expGolombDecoder = new ExpGolomb(ppsData);
    expGolombDecoder.skipUnsignedExpGolomb(); // pps_pic_parameter_set_id
    expGolombDecoder.skipUnsignedExpGolomb(); // pps_seq_parameter_set_id
    expGolombDecoder.skipBits(1); // dependent_slice_segments_enabled_flag
    expGolombDecoder.skipBits(1); // output_flag_present_flag
    expGolombDecoder.skipBits(3); // num_extra_slice_header_bits
    expGolombDecoder.skipBits(1); // sign_data_hiding_enabled_flag
    expGolombDecoder.skipBits(1); // cabac_init_present_flag
    expGolombDecoder.skipUnsignedExpGolomb(); // num_ref_idx_l0_default_active_minus1
    expGolombDecoder.skipUnsignedExpGolomb(); // num_ref_idx_l1_default_active_minus1
    expGolombDecoder.skipExpGolomb(); // init_qp_minus26
    expGolombDecoder.skipBits(1); //  constrained_intra_pred_flag
    expGolombDecoder.skipBits(1); // transform_skip_enabled_flag
    const cu_qp_delta_enabled_flag = expGolombDecoder.readBits(1);
    if (cu_qp_delta_enabled_flag) {
      expGolombDecoder.skipUnsignedExpGolomb(); // diff_cu_qp_delta_depth
    }
    expGolombDecoder.skipExpGolomb(); // pps_cb_qp_offset
    expGolombDecoder.skipExpGolomb(); // pps_cr_qp_offset
    expGolombDecoder.skipBits(1); // pps_slice_chroma_qp_offsets_present_flag
    expGolombDecoder.skipBits(1); // weighted_pred_flag
    expGolombDecoder.skipBits(1); // weighted_bipred_flag
    expGolombDecoder.skipBits(1); // transquant_bypass_enabled_flag
    const tiles_enabled_flag = expGolombDecoder.readBits(1);
    const entropy_coding_sync_enabled_flag = expGolombDecoder.readBits(1);

    if (!tiles_enabled_flag && !entropy_coding_sync_enabled_flag) {
      parallelismType = 1;
    }
    else if (tiles_enabled_flag) {
      parallelismType = 2;
    }
    else if (entropy_coding_sync_enabled_flag) {
      parallelismType = 3;
    }
    else {
      parallelismType = 0;
    }
    avgFrameRate = 0;
    if (vui_timing_info_present_flag) {
      avgFrameRate = Math.round(vui_num_units_in_tick / vui_time_scale * 256);
    }
    constantFrameRate = 0;
    numTemporalLayers = sps_max_sub_layers_minus1 + 1;
    temporalIdNested = sps_temporal_id_nesting_flag;
    lengthSizeMinusOne = 3;


    return {
      generalProfileSpace: generalProfileSpace,
      generalTierFlag: generalTierFlag,
      generalProfileIdc: generalProfileIdc,
      generalProfileCompatibilityFlags: generalProfileCompatibilityFlags,
      generalConstraintIndicatorFlags: generalConstraintIndicatorFlags,
      generalLevelIdc: generalLevelIdc,
      minSpatialSegmentationIdc: minSpatialSegmentationIdc,
      parallelismType: parallelismType,
      chromaFormatIdc: chromaFormatIdc,
      bitDepthLumaMinus8: bitDepthLumaMinus8,
      bitDepthChromaMinus8: bitDepthChromaMinus8,
      avgFrameRate: avgFrameRate,
      constantFrameRate: constantFrameRate,
      numTemporalLayers: numTemporalLayers,
      temporalIdNested: temporalIdNested,
      lengthSizeMinusOne: lengthSizeMinusOne
    };
  };

};
H265Stream.prototype = new Stream();

module.exports = {
  H265Stream: H265Stream,
  NalByteStream: NalByteStream
};
