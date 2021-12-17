import argparse

import cv2

import ImageUtils.ReferencesFetcher as ReferenceFetcher
import matplotlib.pyplot as plt
import ar

RESOURCES_PATH = "../resources/"
MODELS_PATH = RESOURCES_PATH + "models/"
VIDEO_PATH = RESOURCES_PATH + "videos/"


def create_arg_parser():
    # Command line argument parsing
    # NOT ALL OF THEM ARE SUPPORTED YET
    parser = argparse.ArgumentParser(description='Augmented reality application')

    parser.add_argument('-r', '--rectangle', help='draw rectangle delimiting target surface on frame',
                        action='store_true')
    parser.add_argument('-mk', '--model_keypoints', help='draw model keypoints', action='store_true')
    parser.add_argument('-fk', '--frame_keypoints', help='draw frame keypoints', action='store_true')
    parser.add_argument('-ma', '--matches', help='draw matches between keypoints', action='store_true')
    parser.add_argument('-v', '--video', help='videos title')
    parser.add_argument('-ref', '--reference_name', help='references name')
    parser.add_argument('-m', '--model', help='model title')
    parser.add_argument('-o', '--output', help='output video path', default=None)
    return parser


def fetch_obj(args):
    fetcher = ReferenceFetcher.ReferencesFetcher()
    plane, mask = fetcher.fetch(VIDEO_PATH + args.video, args.reference_name)
    ar.ar_main(VIDEO_PATH + args.video, plane, MODELS_PATH + args.model, args)


def main():
    args = create_arg_parser().parse_args()
    fetch_obj(args)


if __name__ == '__main__':
    main()
